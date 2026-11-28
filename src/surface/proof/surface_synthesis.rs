use super::*;
use crate::kernel::MachineBinaryOp;
use crate::kernel::binary_node;
use crate::kernel::{CompareRelation, MachineIntegerType, OverflowOperation};
use crate::kernel::{MachineCastSpelling, cast_term};
use crate::kernel::{OffsetTree as _, OffsetView};
use crate::kernel::{binary_term, unary_term};
use crate::kernel::{
    bits32_constant, constant_i64, constant_u64, int32_constant, int64_constant, uint32_constant,
    uint64_constant,
};

#[cfg(test)]
mod tests;

pub(super) mod folds;
mod matches;
mod pointer_indices;
mod pointer_names;
mod slices;
pub(in crate::surface) use slices::raise_program_slice_operation;

use crate::kernel::program_local_source_name as surface_local_name;
use crate::surface::diagnostics::has_surface_iterator_binding;

const SURFACE_SYNTHESIS_WORK_LIMIT: usize = 16_384;
pub(super) const SURFACE_SYNTHESIS_DEPTH_LIMIT: usize = 128;

#[derive(Clone, Copy)]
struct SurfaceSynthesisBudget {
    remaining_work: usize,
    depth: usize,
    exhausted_category: Option<&'static str>,
}

thread_local! {
    static STRUCTURAL_GOAL_SYNTHESIS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static SYNTHESIS_QUALIFIED_SOURCES: std::cell::RefCell<Option<SurfacePropositionMap>> = const { std::cell::RefCell::new(None) };
    static SYNTHESIS_ENTRY_STATE: std::cell::RefCell<Option<ExecutionState>> = const { std::cell::RefCell::new(None) };
    /// A second reference state, named by its own recorded program point selector
    /// rather than by `old(...)`. A loop back edge needs this: the iteration
    /// entry is neither the function entry nor the current state, and the
    /// ranking members compare the two ends of one iteration.
    static SYNTHESIS_REFERENCE_STATE: std::cell::RefCell<Option<(ExecutionState, ProgramPointSelector)>> = const { std::cell::RefCell::new(None) };
    /// The proof's recorded points. A load registered in a memory that
    /// neither the spelled state nor the entry state reads is spelled at the
    /// point whose memory reads it, found by
    /// [`RecordedStates::point_reading_memory`].
    static SYNTHESIS_RECORDED_POINTS: std::cell::RefCell<Option<RecordedStates>> = const { std::cell::RefCell::new(None) };
    static SURFACE_SYNTHESIS_BUDGET: std::cell::RefCell<Option<SurfaceSynthesisBudget>> =
        const { std::cell::RefCell::new(None) };
    static LAST_SURFACE_SYNTHESIS_EXHAUSTION: std::cell::Cell<Option<&'static str>> =
        const { std::cell::Cell::new(None) };
    static SYNTHESIS_ACTIVE_POINTERS: std::cell::RefCell<std::collections::HashSet<PointerSynthesisKey>> =
        std::cell::RefCell::new(std::collections::HashSet::new());
    static SURFACE_SYNTHESIS_BITVECTOR_NESTING: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
    /// The struct layouts synthesis may read memory through for the
    /// function under proof: its automatic struct-pointer locals and its
    /// `void *` parameters cast to a struct in the sidecar, each by C
    /// spelling. A generated obligation over memory reached through one of
    /// them (the loadability of `job->output[k]`, say) has no written
    /// spelling; this is what lets synthesis name that memory as the field
    /// read the source performs.
    static SYNTHESIS_STRUCT_OWNERS: std::cell::RefCell<Option<std::sync::Arc<SynthesisStructOwners>>> =
        const { std::cell::RefCell::new(None) };
    /// The names the source wrote for kernel quantifier binders, when the
    /// proposition being spelled came from lowering a written quantifier.
    /// A synthesized binder takes its written name instead of a generated
    /// generated one, so a proof focused on the synthesized goal names it
    /// the way the source did.
    static SYNTHESIS_BINDER_NAMES: std::cell::RefCell<Option<std::sync::Arc<BTreeMap<Variable, SurfaceBinder>>>> =
        const { std::cell::RefCell::new(None) };
}

/// Goal production uses only the selected term's indexed names. Speculative
/// local alias selection belongs to premise search, not every rewrite step.
pub(in crate::surface::proof) fn with_structural_goal_synthesis<T>(f: impl FnOnce() -> T) -> T {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            STRUCTURAL_GOAL_SYNTHESIS.with(|slot| slot.set(self.0));
        }
    }
    let _restore = Restore(STRUCTURAL_GOAL_SYNTHESIS.with(|slot| slot.replace(true)));
    f()
}

/// Runs `synthesize` with `names` as the written names of kernel quantifier
/// binders; see `SYNTHESIS_BINDER_NAMES`. A name is used only where it does
/// not collide with a parameter, a local, or an enclosing binder, and the
/// caller still validates the result by lowering it.
pub(in crate::surface) fn with_synthesis_binder_names<T>(
    names: &std::sync::Arc<BTreeMap<Variable, SurfaceBinder>>,
    synthesize: impl FnOnce() -> T,
) -> T {
    struct Restore(Option<std::sync::Arc<BTreeMap<Variable, SurfaceBinder>>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            SYNTHESIS_BINDER_NAMES.with(|slot| {
                slot.replace(self.0.take());
            });
        }
    }
    let _restore = Restore(SYNTHESIS_BINDER_NAMES.with(|slot| slot.replace(Some(names.clone()))));
    synthesize()
}

#[derive(Default)]
pub(in crate::surface) struct SynthesisStructOwners {
    locals: BTreeMap<crate::kernel::BindingName, crate::languages::interface::RecordLayout>,
    cast_parameters: BTreeMap<String, (String, crate::languages::interface::RecordLayout)>,
    callback_sources: std::sync::Arc<BTreeMap<crate::kernel::BindingName, syntax::CExpression>>,
    /// The function's global and static arrays by kernel and source name: the source name and
    /// declared shape an element read is spelled with.
    storage_arrays: BTreeMap<crate::kernel::BindingName, (crate::kernel::BindingName, Vec<u32>)>,
    storage_scalars: BTreeMap<Address, (crate::kernel::BindingName, ProgramType)>,
    /// Declaration spellings for kernel identifiers in retained C arguments.
    storage_source_names: BTreeMap<String, SyntaxTerm>,
}

/// Installs the function's struct owners for synthesis while the guard
/// lives, restoring the previous scope on drop.
pub(in crate::surface) struct LocalStructLayoutScope(Option<std::sync::Arc<SynthesisStructOwners>>);

impl LocalStructLayoutScope {
    pub(in crate::surface) fn enter(
        function: &crate::languages::interface::ImportedFunction,
        block: &FunctionBlock,
    ) -> Self {
        let locals = function
            .local_struct_pointers()
            .iter()
            .filter_map(|(local, struct_name)| {
                Some((local.clone(), function.structs().get(struct_name)?.clone()))
            })
            .collect::<BTreeMap<_, _>>();
        let cast_parameters = block
            .parameter_struct_casts()
            .iter()
            .filter_map(|(parameter, struct_name)| {
                Some((
                    parameter.clone(),
                    (
                        struct_name.clone(),
                        function.structs().get(struct_name)?.clone(),
                    ),
                ))
            })
            .collect::<BTreeMap<_, _>>();
        // The slot index names an array by its source name, or by its
        // kernel name where another object shadows the source name.
        let storage_arrays = function
            .global_arrays()
            .values()
            .filter_map(|array| {
                let spelling = (array.kernel_name().clone(), array.shape()?.to_vec());
                Some([
                    (array.kernel_name().clone(), spelling.clone()),
                    (array.name().into(), spelling),
                ])
            })
            .flatten()
            .chain(function.static_arrays().values().flat_map(|array| {
                let spelling = (array.kernel_name().clone(), array.shape().to_vec());
                [
                    (array.kernel_name().clone(), spelling.clone()),
                    (array.name().into(), spelling),
                ]
            }))
            .collect();
        let storage_scalars = function
            .globals()
            .values()
            .map(|global| {
                (
                    SymbolicMemory::global_pointer(global.kernel_name()),
                    (
                        global.kernel_name().clone(),
                        global.interface_type().to_kernel_type(),
                    ),
                )
            })
            .chain(function.static_locals().values().map(|local| {
                (
                    SymbolicMemory::static_pointer(function.name(), local.kernel_name()),
                    (
                        local.kernel_name().clone(),
                        local.interface_type().to_kernel_type(),
                    ),
                )
            }))
            .collect();
        let storage_source_names = function
            .globals()
            .values()
            .map(|object| (object.kernel_name(), object.name()))
            .chain(
                function
                    .global_arrays()
                    .values()
                    .map(|object| (object.kernel_name(), object.name())),
            )
            .chain(
                function
                    .global_aggregates()
                    .values()
                    .map(|object| (object.kernel_name(), object.name())),
            )
            .chain(
                function
                    .global_aggregate_arrays()
                    .values()
                    .map(|object| (object.kernel_name(), object.name())),
            )
            .chain(
                function
                    .static_locals()
                    .values()
                    .map(|object| (object.kernel_name(), object.name())),
            )
            .chain(
                function
                    .static_arrays()
                    .values()
                    .map(|object| (object.kernel_name(), object.name())),
            )
            .chain(
                function
                    .static_aggregates()
                    .values()
                    .map(|object| (object.kernel_name(), object.name())),
            )
            .filter_map(|(kernel, source)| {
                Some((
                    kernel.named()?.to_owned(),
                    SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                        (source.to_owned()).into(),
                    )),
                ))
            })
            .collect();
        let owners = SynthesisStructOwners {
            storage_source_names,
            storage_scalars,
            locals,
            cast_parameters,
            callback_sources: function.callback_statement_sources().clone(),
            storage_arrays,
        };
        Self(SYNTHESIS_STRUCT_OWNERS.with(|slot| slot.replace(Some(std::sync::Arc::new(owners)))))
    }
}

/// Restore declaration names in one retained call argument. This traverses
/// only that argument and performs indexed name lookups; it never synthesizes
/// an alias from facts or memory history.
pub(in crate::surface) fn source_c_argument(argument: &ProgramExpression) -> ProgramExpression {
    SYNTHESIS_STRUCT_OWNERS.with(|slot| {
        let owners = slot.borrow();
        let owners = owners
            .as_ref()
            .expect("call argument has a function source scope");
        crate::surface::lowering::substitute_program_expression(
            argument,
            &owners.storage_source_names,
        )
        .expect("declaration names are C fragments")
    })
}

pub(in crate::surface) fn callback_source_name(name: &str) -> Option<String> {
    SYNTHESIS_STRUCT_OWNERS.with(|slot| {
        let owners = slot.borrow();
        let expression = owners.as_ref()?.callback_sources.get(&name.into())?;
        Some(crate::surface::diagnostics::describe_callback_source(
            expression,
        ))
    })
}

impl Drop for LocalStructLayoutScope {
    fn drop(&mut self) {
        SYNTHESIS_STRUCT_OWNERS.with(|slot| {
            slot.replace(self.0.take());
        });
    }
}

/// One object synthesis may spell field reads through: how its pointer is
/// written, the pointer's value here, and the struct layout at that value.
struct StructOwner {
    base: ProgramExpression,
    pointer: crate::kernel::Pointer,
    layout: crate::languages::interface::RecordLayout,
}

/// The cast `void *` parameters, with their argument values, and the
/// struct-pointer locals present in this state. Declared struct-pointer
/// parameters keep their own parameter-based spelling paths.
fn struct_owners(
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Vec<StructOwner> {
    let Some(owners) = SYNTHESIS_STRUCT_OWNERS.with(|slot| slot.borrow().clone()) else {
        return Vec::new();
    };
    let mut found = Vec::new();
    for (parameter, argument) in parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
    {
        let (Some((struct_name, layout)), ProgramExpression::Value(ProgramValue::Pointer(base))) =
            (owners.cast_parameters.get(parameter.name()), argument)
        else {
            continue;
        };
        found.push(StructOwner {
            base: ProgramExpression::Cast {
                expression: Box::new(ProgramExpression::Variable(
                    crate::surface::surface_parameter_binding(parameter.binding_name()),
                )),
                target_type: ProgramType::Int32Pointer,
                integer_mode: crate::kernel::IntegerCastMode::Standard,
                pointee_struct: Some(struct_name.clone()),
                pointee_struct_size: Some(layout.size_bytes()),
                pointee_volatile: false,
                pointee_constant: false,
                explicit_qualification: false,
            },
            pointer: base.clone(),
            layout: layout.clone(),
        });
    }
    for (name, value) in state.locals().object_values() {
        if value.pointer().is_none() {
            continue;
        }
        let native = value.native();
        if let (Some(layout), ProgramValue::Pointer(base)) =
            (owners.locals.get(name), native.as_ref())
        {
            found.push(StructOwner {
                base: ProgramExpression::Variable(surface_local_name(name)),
                pointer: base.clone(),
                layout: layout.clone(),
            });
        }
    }
    found
}

/// A program parameter or local raised as a Surface operand: `program::name`
/// where its name is also a Click value (`result`, `iterations`), so it
/// lowers to the program's binding rather than that value; otherwise the
/// C expression itself. Only a caller that knows `expression` names a
/// program binding uses this: the same name can also carry the contract
/// result.
fn program_operand(expression: ProgramExpression) -> SyntaxTerm {
    match &expression {
        ProgramExpression::Variable(name) if crate::surface::is_click_value_name(name.clone()) => {
            SyntaxTerm::ProgramBinding(name.to_string())
        }
        _ => SyntaxTerm::ProgramExpression(expression),
    }
}

fn owner_field_pointer(
    base: &ProgramExpression,
    offset: impl Into<crate::kernel::LayoutOffset>,
) -> ProgramExpression {
    let offset = offset.into();
    if offset.bytes() == Some(0) {
        base.clone()
    } else {
        ProgramExpression::PointerOffsetBytes {
            pointer: Box::new(base.clone()),
            bytes: offset,
        }
    }
}

/// A range base synthesis can name: a parameter or local by its spelling,
/// or a pointer field read through a struct-pointer parameter or local.
struct NamedRangeBase {
    lowered: ProgramExpression,
    surface: SyntaxTerm,
    pointer: crate::kernel::Pointer,
    width: u32,
}

fn range_struct_owners(
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Vec<StructOwner> {
    let mut owners: Vec<StructOwner> = Vec::new();
    for (parameter, argument) in parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
    {
        if let (Some(layout), ProgramExpression::Value(ProgramValue::Pointer(base))) = (
            parameter
                .pointee_struct_layout()
                .or_else(|| parameter.struct_layout()),
            argument,
        ) {
            owners.push(StructOwner {
                base: ProgramExpression::Variable(crate::surface::surface_parameter_binding(
                    parameter.binding_name(),
                )),
                pointer: base.clone(),
                layout: layout.clone(),
            });
        }
    }
    owners.extend(struct_owners(parameter_binding, state));
    owners
}

/// Spell a byte span inside a declared struct as an exact field slot. A
/// shorter span excludes the field's padding, so it needs an explicit byte
/// pointer instead; a range on the struct pointer would count whole structs.
fn synthesize_struct_loadable_segment(
    base: &Address,
    bytes: &OldMachineTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Option<SyntaxProposition> {
    let bytes = bytes.as_const()?;
    for owner in range_struct_owners(parameter_binding, state) {
        let Some(start) = base
            .element_index_from_base_with_width(&owner.pointer, 1)
            .and_then(|index| index.as_const())
        else {
            continue;
        };
        let Some(end) = start
            .checked_add(bytes)
            .filter(|end| *end <= owner.layout.size_bytes())
        else {
            continue;
        };
        for (name, field) in owner.layout.fields() {
            if start != field.offset_bytes() {
                continue;
            }
            let slot_end = owner
                .layout
                .fields()
                .values()
                .map(crate::languages::interface::RecordField::offset_bytes)
                .filter(|offset| *offset > field.offset_bytes())
                .min()
                .unwrap_or_else(|| owner.layout.size_bytes());
            if end != slot_end
                || field.array_shape().is_some()
                || field.struct_name().is_some()
                || field.union_name().is_some()
            {
                continue;
            }
            let width = match field.interface_type() {
                InterfaceType::Char(_) | InterfaceType::UInt8 | InterfaceType::Int8 => 1,
                InterfaceType::Int16 | InterfaceType::UInt16 => 2,
                InterfaceType::Int64(_) | InterfaceType::UInt64(_) | InterfaceType::Float64 => 8,
                _ => 4,
            };
            if !start.is_multiple_of(width) || !end.is_multiple_of(width) {
                continue;
            }
            return Some(SyntaxProposition::Loadable {
                segment: ContractSegment {
                    uninitialized: false,
                    state: ContractSegmentState::Current,
                    base: owner.base,
                    start: ProgramExpression::Value(int32(start / width)),
                    end: ProgramExpression::Value(int32(end / width)),
                    surface: ContractSegmentSurface::Field {
                        value_bytes: Some(width),
                        base: None,
                        name: name.clone(),
                        element_width: Some(width),
                        element_type: Some(field.interface_type().to_kernel_type()),
                    },
                },
            });
        }
        let cast = ProgramExpression::Cast {
            expression: Box::new(owner.base),
            target_type: ProgramType::UInt8Pointer,
            integer_mode: crate::kernel::IntegerCastMode::Standard,
            pointee_struct: None,
            pointee_struct_size: None,
            pointee_volatile: false,
            pointee_constant: false,
            explicit_qualification: false,
        };
        let start = ProgramExpression::Value(int32(start));
        let end = ProgramExpression::Value(int32(end));
        return Some(SyntaxProposition::Loadable {
            segment: ContractSegment {
                uninitialized: false,
                state: ContractSegmentState::Current,
                base: cast.clone(),
                start: start.clone(),
                end: end.clone(),
                surface: ContractSegmentSurface::Range {
                    base: SyntaxTerm::ProgramExpression(cast),
                    start: SyntaxTerm::ProgramExpression(start),
                    end: SyntaxTerm::ProgramExpression(end),
                },
            },
        });
    }
    None
}

/// Pointer-typed fields of struct-pointer parameters and locals whose cell
/// currently holds a data pointer, spelled as the field read. The struct
/// layouts come from the parameter declarations and the installed local
/// layout scope; the pointer values come from this state's memory.
fn field_pointer_bases(
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Vec<NamedRangeBase> {
    let owners = range_struct_owners(parameter_binding, state);
    let mut bases = Vec::new();
    for owner in owners {
        for (field_name, field) in owner.layout.fields() {
            let value_type = field.interface_type().to_kernel_type();
            let Some(width) = value_type.pointee_type().map(ProgramType::byte_width) else {
                continue;
            };
            if width == 0 {
                continue;
            }
            let field_pointer = owner.pointer.offset_by_bytes(field.offset_bytes());
            let loaded = match state.memory().load(&field_pointer) {
                ExpressionOutcome::Value(ProgramValue::Pointer(loaded)) => loaded,
                // Contract memory can keep a pointer field as the
                // pointer-width load of the field: the pointer it names is
                // that read.
                ExpressionOutcome::Value(ProgramValue::Int32(value)) => {
                    let Some(pointer) = Address::loaded(&value) else {
                        continue;
                    };
                    let ProgramValue::Pointer(loaded) =
                        ProgramValue::typed_pointer(pointer, value_type)
                    else {
                        continue;
                    };
                    loaded
                }
                _ => continue,
            };
            let lowered = ProgramExpression::TypedLoad {
                pointer: Box::new(owner_field_pointer(&owner.base, field.offset_bytes())),
                value_type,
                volatile: false,
                pointee_constant: false,
                access_class: None,
                source: Default::default(),
            };
            bases.push(NamedRangeBase {
                surface: SyntaxTerm::Field {
                    pointee_struct: None,
                    base: Box::new(SyntaxTerm::ProgramExpression(owner.base.clone())),
                    field: field_name.clone(),
                    lowered: lowered.clone(),
                    offset_bytes: field.offset_bytes().into(),
                },
                lowered,
                pointer: loaded,
                width,
            });
        }
    }
    bases
}

fn named_range_bases(
    parameter_binding: ParameterBinding<'_>,
    state: Option<&ExecutionState>,
    full_state: &ExecutionState,
) -> Vec<NamedRangeBase> {
    let mut bases = named_pointer_bases(parameter_binding, state)
        .map(|(lowered, pointer, width)| NamedRangeBase {
            surface: SyntaxTerm::ProgramExpression(lowered.clone()),
            lowered,
            pointer,
            width,
        })
        .collect::<Vec<_>>();
    bases.extend(field_pointer_bases(parameter_binding, full_state));
    bases
}

pub(super) struct QualifiedSynthesisScope(Option<SurfacePropositionMap>);

impl QualifiedSynthesisScope {
    pub(super) fn enter(sources: &SurfacePropositionMap) -> Self {
        Self(SYNTHESIS_QUALIFIED_SOURCES.with(|slot| slot.replace(Some(sources.clone()))))
    }
}

impl Drop for QualifiedSynthesisScope {
    fn drop(&mut self) {
        SYNTHESIS_QUALIFIED_SOURCES.with(|slot| slot.replace(self.0.take()));
    }
}

struct SynthesisEntryScope(Option<ExecutionState>);
impl Drop for SynthesisEntryScope {
    fn drop(&mut self) {
        SYNTHESIS_ENTRY_STATE.with(|slot| {
            slot.replace(self.0.take());
        });
    }
}

pub(in crate::surface) fn synthesize_surface_proposition_at_entry_and_post(
    proposition: &Proposition,
    parameter_binding: ParameterBinding<'_>,
    entry: &ExecutionState,
    post: &ExecutionState,
) -> Option<SyntaxProposition> {
    let _entry =
        SynthesisEntryScope(SYNTHESIS_ENTRY_STATE.with(|slot| slot.replace(Some(entry.clone()))));
    synthesize_surface_proposition(proposition, parameter_binding, post)
}

/// [`synthesize_surface_value`] at `state`, spelling a value only the
/// function's entry holds as `old(...)`.
pub(in crate::surface) fn synthesize_surface_value_at_entry_and_post(
    value: &ProgramValue,
    parameter_binding: ParameterBinding<'_>,
    entry: Option<&ExecutionState>,
    state: &ExecutionState,
) -> Option<SyntaxTerm> {
    let _entry = entry.map(|entry| {
        SynthesisEntryScope(SYNTHESIS_ENTRY_STATE.with(|slot| slot.replace(Some(entry.clone()))))
    });
    synthesize_surface_value(value, parameter_binding, state)
}

/// [`synthesize_surface_proposition_at_entry_and_post`] with names for
/// bound variables.
pub(in crate::surface) fn synthesize_surface_proposition_at_entry_post_with_bound_variable_names(
    proposition: &Proposition,
    parameter_binding: ParameterBinding<'_>,
    entry: &ExecutionState,
    post: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxProposition> {
    let _entry =
        SynthesisEntryScope(SYNTHESIS_ENTRY_STATE.with(|slot| slot.replace(Some(entry.clone()))));
    synthesize_surface_proposition_with_bound_variable_names(
        proposition,
        parameter_binding,
        post,
        bound_variables,
    )
}

/// As above, plus one further reference state addressed by a recorded
/// program point selector. A value the current state no longer holds but the
/// state state does reads as `at(<selector>, name)`, which is the same
/// spelling loop-body premises already use, so the synthesized form lowers
/// back to exactly this term at the state the selector names.
pub(in crate::surface) fn synthesize_surface_proposition_at_entry_post_and_state(
    proposition: &Proposition,
    parameter_binding: ParameterBinding<'_>,
    entry: &ExecutionState,
    post: &ExecutionState,
    retained_state: Option<(&ExecutionState, &ProgramPointSelector)>,
) -> Option<SyntaxProposition> {
    let _state = SynthesisReferenceStateScope(SYNTHESIS_REFERENCE_STATE.with(|slot| {
        slot.replace(retained_state.map(|(state, selector)| (state.clone(), selector.clone())))
    }));
    synthesize_surface_proposition_at_entry_and_post(proposition, parameter_binding, entry, post)
}

struct SynthesisReferenceStateScope(Option<(ExecutionState, ProgramPointSelector)>);
impl Drop for SynthesisReferenceStateScope {
    fn drop(&mut self) {
        SYNTHESIS_REFERENCE_STATE.with(|slot| {
            slot.replace(self.0.take());
        });
    }
}

/// Spells loads registered at the proof's recorded points while alive.
pub(in crate::surface) struct SynthesisRecordedPointsScope(Option<RecordedStates>);

impl SynthesisRecordedPointsScope {
    pub(in crate::surface) fn enter(points: &RecordedStates) -> Self {
        Self(SYNTHESIS_RECORDED_POINTS.with(|slot| slot.replace(Some(points.clone()))))
    }
}

impl Drop for SynthesisRecordedPointsScope {
    fn drop(&mut self) {
        SYNTHESIS_RECORDED_POINTS.with(|slot| {
            slot.replace(self.0.take());
        });
    }
}

/// The recorded state whose structural read selection reproduces this read:
/// the point recording its memory, or the projection's source memory.
fn recorded_point_of_load(
    read: &OldMachineTerm,
) -> Option<(ProgramPointSelector, ExecutionState, OldMachineTerm)> {
    let OldMachineTerm::MemoryLoad(memory, pointer, _) = read else {
        return None;
    };
    SYNTHESIS_RECORDED_POINTS.with(|slot| {
        use crate::surface::proof::raise_lower_audit::note_reason;
        let slot = slot.borrow();
        let Some((selector, state)) = slot.as_ref()?.point_reading_load(memory, pointer) else {
            note_reason(|| {
                format!(
                    "snapshot read: its memory matches no recorded point (read site: {})",
                    if memory.read_site().is_some() {
                        "yes"
                    } else {
                        "no"
                    }
                )
            });
            return None;
        };
        let Some(load) = scalar_read_in_state(read, state) else {
            note_reason(|| {
                "snapshot read: the recorded point with its memory names the cell differently"
                    .to_string()
            });
            return None;
        };
        Some((selector.clone(), state.clone(), load))
    })
}

/// An indexed algebraic load names the value held by a local at its
/// defining write. Check the local's read before offering its spelling.
fn synthesize_point_held_value(
    ty: &crate::kernel::AlgebraicType,
    point: &crate::kernel::ProgramPoint,
    pointer: &Address,
    state: &ExecutionState,
) -> Option<SyntaxTerm> {
    let raise = |selected: &ExecutionState| {
        let name = selected.locals().name_for_slot(pointer)?;
        let ProgramValue::Parameter(held) = selected.held_local_value(name)? else {
            return None;
        };
        let crate::kernel::AlgebraicTermNode::MemoryLoad {
            point: held_point,
            pointer: held_pointer,
        } = &held.node
        else {
            return None;
        };
        (&held.algebraic_type == ty && held_point == point && held_pointer.as_ref() == pointer)
            .then(|| SyntaxTerm::ProgramExpression(ProgramExpression::Variable(name.clone())))
    };
    raise(state).or_else(|| synthesize_at_program_point(point, state, raise))
}

fn synthesize_point_algebraic_read(
    ty: &crate::kernel::AlgebraicType,
    point: &crate::kernel::ProgramPoint,
    pointer: &Address,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    synthesize_point_held_value(ty, point, pointer, state).or_else(|| {
        if !ty.rigid {
            return None;
        }
        synthesize_point_read(
            point,
            pointer,
            ProgramType::Parameter(crate::kernel::TypeParameterName::of(ty)),
            parameter_binding,
            state,
            bound_variables,
        )
    })
}

/// The name of the local that keeps `term` in its object at `pointer`, in
/// `state`: a borrowed Rust enum local `o` read there is spelled `o`. The
/// local's name reads its object at the point it was last written
/// ([`ExecutionState::held_local_value`]), so it spells exactly that read.
fn synthesize_held_value_local(
    term: &crate::kernel::AlgebraicTerm,
    pointer: &Address,
    state: &ExecutionState,
) -> Option<SyntaxTerm> {
    let (name, _, _) = state.locals().held_value_locals().find(|(_, _, slot)| {
        crate::instrumentation::record_deterministic_work(1);
        *slot == pointer
    })?;
    matches!(state.held_local_value(name), Some(ProgramValue::Parameter(held)) if held.as_ref() == term)
        .then(|| SyntaxTerm::ProgramExpression(ProgramExpression::Variable(name.clone())))
}

/// `at(point, o)` for a read of a held-value local's object that no nearer
/// state names: the recorded point whose memory reads that version.
fn synthesize_recorded_held_value_local(
    term: &crate::kernel::AlgebraicTerm,
    pointer: &Address,
) -> Option<SyntaxTerm> {
    let crate::kernel::AlgebraicTermNode::MemoryLoad {
        point: memory,
        pointer: address,
    } = &term.node
    else {
        return None;
    };
    SYNTHESIS_RECORDED_POINTS.with(|slot| {
        let slot = slot.borrow();
        let (selector, recorded) = slot.as_ref()?.point_reading_load(memory, address)?;
        Some(SyntaxTerm::At {
            selector: selector.clone(),
            expression: Box::new(synthesize_held_value_local(term, pointer, recorded)?),
        })
    })
}

/// `at(point, read)` for a load variable no nearer state names.
fn synthesize_load_at_recorded_point(
    variable: &Variable,
    parameter_binding: ParameterBinding<'_>,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let read = crate::kernel::registered_load_term_for_variable(variable)?;
    synthesize_read_at_recorded_point(&read, parameter_binding, bound_variables)
}

fn synthesize_read_at_recorded_point(
    read: &OldMachineTerm,
    parameter_binding: ParameterBinding<'_>,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let (selector, state, load) = recorded_point_of_load(read)?;
    let expression =
        synthesize_surface_bitvector(&load, parameter_binding, &state, bound_variables)?;
    Some(SyntaxTerm::At {
        selector,
        expression: Box::new(expression),
    })
}

/// The `at(<selector>, name)` spelling of a term the state state's own
/// scalar local holds exactly. Only a term the current state cannot name
/// reaches this, so the state spelling never shadows a current name.
fn synthesize_state_local(term: &OldMachineTerm) -> Option<SyntaxTerm> {
    SYNTHESIS_REFERENCE_STATE.with(|slot| {
        let slot = slot.borrow();
        let (state, selector) = slot.as_ref()?;
        let name = state.locals().names_holding_integer(term).find(|name| {
            state.locals().get(*name).is_some_and(|value| {
                crate::kernel::MachineIntegerType::from_program_type(value.program_type()).is_some()
            })
        })?;
        if !has_surface_iterator_binding(name) {
            return None;
        }
        if let Some(result) = SYNTHESIS_RECORDED_POINTS.with(|slot| {
            slot.borrow().as_ref()?.call_capture_expression(
                name,
                state.locals().get(name)?,
                Some(selector),
            )
        }) {
            return Some(result);
        }
        Some(SyntaxTerm::At {
            selector: selector.clone(),
            expression: Box::new(if crate::surface::is_click_value_name(name) {
                SyntaxTerm::ProgramBinding(name.to_string())
            } else {
                SyntaxTerm::ProgramExpression(ProgramExpression::Variable(surface_local_name(name)))
            }),
        })
    })
}

/// The `at(point, name)` spelling of a term a scalar local held at a
/// recorded point: the point where the value was introduced, found in one
/// index lookup. Only a term no nearer state names reaches this.
fn synthesize_recorded_local(term: &OldMachineTerm) -> Option<SyntaxTerm> {
    SYNTHESIS_RECORDED_POINTS.with(|slot| {
        let slot = slot.borrow();
        let points = slot.as_ref()?;
        let (selector, name, state) = points.point_naming_integer(term)?;
        if !has_surface_iterator_binding(name) {
            return None;
        }
        if let Some(result) = state
            .locals()
            .get(name)
            .and_then(|value| points.call_capture_expression(name, value, Some(selector)))
        {
            return Some(result);
        }
        Some(SyntaxTerm::At {
            selector: selector.clone(),
            expression: Box::new(if crate::surface::is_click_value_name(name) {
                SyntaxTerm::ProgramBinding(name.to_string())
            } else {
                SyntaxTerm::ProgramExpression(ProgramExpression::Variable(surface_local_name(name)))
            }),
        })
    })
}

/// `at(point, e)` for a term a memory cell held at a recorded point, where
/// `e` spells it in that point's state: the field or element it is there.
/// The recorded points are cleared for the inner spelling, so it never
/// nests.
fn synthesize_recorded_cell_value(
    term: &OldMachineTerm,
    parameter_binding: ParameterBinding<'_>,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let candidates = SYNTHESIS_RECORDED_POINTS.with(|slot| {
        let slot = slot.borrow();
        Some(
            slot.as_ref()?
                .points_holding_cell_integer(term)
                .map(|(selector, state)| (selector.clone(), state.clone()))
                .collect::<Vec<_>>(),
        )
    })?;
    if candidates.is_empty() {
        return None;
    }
    let points = SYNTHESIS_RECORDED_POINTS.with(|slot| slot.replace(None));
    let spelled = candidates.into_iter().find_map(|(selector, state)| {
        Some(SyntaxTerm::At {
            selector,
            expression: Box::new(synthesize_surface_bitvector(
                term,
                parameter_binding,
                &state,
                bound_variables,
            )?),
        })
    });
    SYNTHESIS_RECORDED_POINTS.with(|slot| slot.replace(points));
    spelled
}

struct SurfaceSynthesisScope(Option<SurfaceSynthesisBudget>);

impl SurfaceSynthesisScope {
    fn enter() -> Self {
        LAST_SURFACE_SYNTHESIS_EXHAUSTION.with(|last| last.set(None));
        let previous = SURFACE_SYNTHESIS_BUDGET.with(|slot| {
            slot.replace(Some(SurfaceSynthesisBudget {
                remaining_work: SURFACE_SYNTHESIS_WORK_LIMIT,
                depth: 0,
                exhausted_category: None,
            }))
        });
        Self(previous)
    }
}

impl Drop for SurfaceSynthesisScope {
    fn drop(&mut self) {
        let exhausted = SURFACE_SYNTHESIS_BUDGET.with(|slot| {
            let current = slot.replace(self.0.take());
            current.and_then(|budget| budget.exhausted_category)
        });
        if exhausted.is_some() {
            LAST_SURFACE_SYNTHESIS_EXHAUSTION.with(|last| last.set(exhausted));
        }
    }
}

struct SurfaceSynthesisFrame {
    counted: bool,
}

// Spelling an offset may ask for the address currently being spelled.
// Reject that candidate edge; another local can still name the pointer.
#[derive(Clone, Eq, PartialEq, Hash)]
struct PointerSynthesisKey {
    pointer: Address,
    state: usize,
    parameters: usize,
    arguments: usize,
    bound_variables: usize,
}

struct SurfacePointerFrame(PointerSynthesisKey);

impl SurfacePointerFrame {
    fn enter(
        pointer: &Address,
        parameter_binding: ParameterBinding<'_>,
        state: &ExecutionState,
        bound_variables: &BTreeMap<Variable, SurfaceBinder>,
    ) -> Option<Self> {
        // All borrowed inputs remain live for this frame. Their addresses
        // distinguish state and binder environments without cloning or
        // structurally hashing the surrounding proof state.
        crate::instrumentation::record_deterministic_work(1);
        let key = PointerSynthesisKey {
            pointer: pointer.clone(),
            state: state as *const _ as usize,
            parameters: parameter_binding.parameters.as_ptr() as usize,
            arguments: parameter_binding.arguments.as_ptr() as usize,
            bound_variables: bound_variables as *const _ as usize,
        };
        SYNTHESIS_ACTIVE_POINTERS
            .with(|active| active.borrow_mut().insert(key.clone()).then(|| Self(key)))
    }
}

impl Drop for SurfacePointerFrame {
    fn drop(&mut self) {
        SYNTHESIS_ACTIVE_POINTERS.with(|active| {
            active.borrow_mut().remove(&self.0);
        });
    }
}

struct SurfaceBitvectorFrame {
    outermost: bool,
}

impl SurfaceBitvectorFrame {
    fn enter() -> Self {
        let outermost = SURFACE_SYNTHESIS_BITVECTOR_NESTING.with(|depth| {
            let outermost = depth.get() == 0;
            depth.set(depth.get() + 1);
            outermost
        });
        Self { outermost }
    }

    fn is_outermost(&self) -> bool {
        self.outermost
    }
}

impl Drop for SurfaceBitvectorFrame {
    fn drop(&mut self) {
        SURFACE_SYNTHESIS_BITVECTOR_NESTING.with(|depth| {
            depth.set(depth.get().saturating_sub(1));
        });
    }
}

impl SurfaceSynthesisFrame {
    fn enter(category: &'static str) -> Option<Self> {
        let counted = SURFACE_SYNTHESIS_BUDGET.with(|slot| {
            let mut slot = slot.borrow_mut();
            let Some(budget) = slot.as_mut() else {
                return Some(false);
            };
            if budget.remaining_work == 0 || budget.depth >= SURFACE_SYNTHESIS_DEPTH_LIMIT {
                budget.exhausted_category.get_or_insert(category);
                return None;
            }
            budget.remaining_work -= 1;
            budget.depth += 1;
            Some(true)
        })?;
        Some(Self { counted })
    }
}

impl Drop for SurfaceSynthesisFrame {
    fn drop(&mut self) {
        if self.counted {
            SURFACE_SYNTHESIS_BUDGET.with(|slot| {
                if let Some(budget) = slot.borrow_mut().as_mut() {
                    budget.depth = budget.depth.saturating_sub(1);
                }
            });
        }
    }
}

fn consume_surface_synthesis_work(category: &'static str) -> bool {
    SURFACE_SYNTHESIS_BUDGET.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(budget) = slot.as_mut() else {
            return true;
        };
        if budget.remaining_work == 0 {
            budget.exhausted_category.get_or_insert(category);
            return false;
        }
        budget.remaining_work -= 1;
        true
    })
}

fn record_surface_synthesis_exhaustion(category: &'static str) {
    SURFACE_SYNTHESIS_BUDGET.with(|slot| {
        if let Some(budget) = slot.borrow_mut().as_mut() {
            budget.exhausted_category.get_or_insert(category);
        }
    });
}

fn bitvector_term_exceeds_depth_limit(root: &OldMachineTerm) -> bool {
    bitvector_term_exceeds_depth_limit_from(root, 0)
}

/// Whether an address offset that is one scaled index has a path below the
/// index, entered at `depth`, that reaches the depth limit.
fn scaled_index_exceeds_depth_limit(offset: &AddressOffset, depth: usize) -> bool {
    match offset.view() {
        OffsetView::Int32Scaled { index, .. } | OffsetView::Int64Scaled { index, .. } => {
            bitvector_term_exceeds_depth_limit_from(index.structural_value(), depth)
        }
        _ => false,
    }
}

/// Whether some path below `root`, entered at `depth`, reaches the depth
/// limit. An address's scaled index is owned by its offset view, so its
/// operand is checked by a nested walk; the answer does not depend on order.
fn bitvector_term_exceeds_depth_limit_from(root: &OldMachineTerm, depth: usize) -> bool {
    let mut pending = vec![(root, depth)];
    while let Some((term, depth)) = pending.pop() {
        if depth >= SURFACE_SYNTHESIS_DEPTH_LIMIT.saturating_sub(1) {
            return true;
        }
        match term {
            OldMachineTerm::ThreadHandle(_) | OldMachineTerm::PureApplicationCount(_) => {}
            crate::kernel::binary_machine_term!(left, right) => {
                pending.push((left, depth + 1));
                pending.push((right, depth + 1));
            }
            OldMachineTerm::Float32Binary { left, right, .. }
            | OldMachineTerm::Float64Binary { left, right, .. } => {
                pending.push((left, depth + 1));
                pending.push((right, depth + 1));
            }
            crate::kernel::unary_machine_term!(value) => {
                pending.push((value, depth + 1));
            }
            OldMachineTerm::If {
                then_term,
                else_term,
                ..
            } => {
                pending.push((then_term, depth + 1));
                pending.push((else_term, depth + 1));
            }
            OldMachineTerm::RangeFold {
                start,
                end,
                initial,
                body,
                ..
            } => {
                pending.push((start, depth + 1));
                pending.push((end, depth + 1));
                pending.push((initial, depth + 1));
                pending.push((body, depth + 1));
            }
            OldMachineTerm::PureFunctionApplication { arguments, .. } => {
                pending.extend(arguments.iter().map(|argument| (argument, depth + 1)));
            }
            OldMachineTerm::ClickFunctionApplication { .. }
            | OldMachineTerm::AlgebraicMatch { .. }
            | OldMachineTerm::IntegerToMachine { .. }
            | OldMachineTerm::BoolCast { .. } => {}
            OldMachineTerm::MemoryLoad(_, pointer, _) => {
                if scaled_index_exceeds_depth_limit(&pointer.offset, depth + 1) {
                    return true;
                }
            }
            OldMachineTerm::IntegerAddress(pointer, _) => {
                if scaled_index_exceeds_depth_limit(&pointer.offset, depth + 1) {
                    return true;
                }
            }
            OldMachineTerm::Constant { .. } | OldMachineTerm::Variable(_) => {}
        }
    }
    false
}

pub(in crate::surface) fn synthesize_surface_proposition(
    proposition: &Proposition,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Option<SyntaxProposition> {
    let _scope = SurfaceSynthesisScope::enter();
    synthesize_surface_proposition_with_guard_fallback(
        proposition,
        parameter_binding,
        state,
        &BTreeMap::new(),
    )
}

/// The disequality of two array element indices a store compares (or a
/// pointer disequality's two element addresses differ by), spelled as a
/// comparison of the index words: `((m - 1) as int32) != 0` for `int32`
/// indices, `((n - 1u64) as uint64) != 0u64` or `j != 0u64` for `uint64`
/// ones. Each word is spelled as [`synthesize_surface_bitvector`] spells it;
/// a word that spells as arithmetic is converted to its format with `as`,
/// since Click arithmetic on C operands is Integer arithmetic and the store
/// compares the wrapped word. The caller states it for the kernel comparison
/// it built from the same two words; the requirement's round trip checks the
/// lowering.
pub(in crate::surface) fn synthesize_store_index_disequality(
    store_index: &OldMachineTerm,
    cell_index: &OldMachineTerm,
    format: MachineIntegerType,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxProposition> {
    let _scope = SurfaceSynthesisScope::enter();
    let word = |term: &OldMachineTerm| {
        let expression =
            synthesize_surface_bitvector(term, parameter_binding, state, bound_variables)?;
        let ctype = match format {
            MachineIntegerType::Int32 => ProgramType::Int32,
            MachineIntegerType::Int64 => ProgramType::Int64,
            MachineIntegerType::UInt64 => ProgramType::UInt64,
            _ => return None,
        };
        if matches!(
            expression,
            SyntaxTerm::Add(..) | SyntaxTerm::Subtract(..) | SyntaxTerm::Multiply(..)
        ) {
            synthesize_observation_operand(expression, ctype)
        } else {
            Some(expression)
        }
    };
    // Both words are spelled before either refusal is read: synthesis
    // charges work.
    let left = word(store_index);
    let right = word(cell_index);
    Some(SyntaxProposition::Comparison {
        left: left?,
        operator: ComparisonOperator::NotEqual,
        right: right?,
    })
}

/// The source spelling of one machine term, for a diagnostic that has to name
/// the written subterm a generated condition came from.
///
/// This is the same bounded reconstruction [`synthesize_surface_proposition`]
/// performs on a proposition's operands, exposed so a message can print
/// `hi - 1` instead of `v2 - 1`. It is read-only: nothing here is offered to a
/// proof step, so no candidate needs validating against a kernel form.
pub(in crate::surface) fn synthesize_surface_machine_expression(
    term: &OldMachineTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Option<SyntaxTerm> {
    let _scope = SurfaceSynthesisScope::enter();
    synthesize_surface_bitvector(term, parameter_binding, state, &BTreeMap::new())
}

thread_local! {
    /// The kernel variables the proof's own binders (`let`, `choose`,
    /// `obtain`, `unfold`) name. A C local or parameter holding the same
    /// value is spelled first, since it carries its declared type; these
    /// name what no C name holds.
    static PROOF_BINDER_NAMES: std::cell::RefCell<std::sync::Arc<BTreeMap<Variable, SurfaceBinder>>> =
        std::cell::RefCell::new(std::sync::Arc::default());
}

/// Runs `operation` with `names` as the proof binders' names; see
/// `PROOF_BINDER_NAMES`.
pub(in crate::surface) fn with_proof_binder_names<R>(
    names: std::sync::Arc<BTreeMap<Variable, SurfaceBinder>>,
    operation: impl FnOnce() -> R,
) -> R {
    struct Restore(std::sync::Arc<BTreeMap<Variable, SurfaceBinder>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            let previous = std::mem::take(&mut self.0);
            PROOF_BINDER_NAMES.with(|names| *names.borrow_mut() = previous);
        }
    }
    let _restore = Restore(PROOF_BINDER_NAMES.with(|current| current.replace(names)));
    operation()
}

thread_local! {
    static PROOF_BINDING_NAMES: std::cell::RefCell<(
        super::proof_object::binding_names::BindingNames,
        PersistentBinderMap<SyntaxTerm>,
    )> = std::cell::RefCell::new((
        super::proof_object::binding_names::BindingNames::default(),
        PersistentBinderMap::default(),
    ));
}

pub(super) struct ProofBindingNamesScope(
    super::proof_object::binding_names::BindingNames,
    PersistentBinderMap<SyntaxTerm>,
);
impl ProofBindingNamesScope {
    pub(super) fn enter(
        names: super::proof_object::binding_names::BindingNames,
        shadows: PersistentBinderMap<SyntaxTerm>,
    ) -> Self {
        let (names, shadows) = PROOF_BINDING_NAMES.with(|slot| slot.replace((names, shadows)));
        Self(names, shadows)
    }
}
impl Drop for ProofBindingNamesScope {
    fn drop(&mut self) {
        PROOF_BINDING_NAMES.with(|slot| {
            slot.replace((std::mem::take(&mut self.0), std::mem::take(&mut self.1)));
        });
    }
}

fn proof_binder_name(variable: Variable) -> Option<SurfaceBinder> {
    PROOF_BINDER_NAMES
        .with(|names| names.borrow().get(&variable).cloned())
        .or_else(|| {
            PROOF_BINDING_NAMES.with(|slot| {
                let (names, shadows) = &*slot.borrow();
                let name = names.name(variable)?;
                // An intro may shadow a proof-local name. Its selected binding,
                // rather than an ambient alias search, decides whether it is live.
                if shadows.get(name).is_some_and(|expression| {
                    super::proof_object::binding_names::variable(expression) != Some(variable)
                }) {
                    return None;
                }
                Some(name.to_owned())
            })
        })
}

thread_local! {
    static PROOF_LOCAL_VALUE_NAMES: std::cell::RefCell<Vec<pointer_names::NamedValue>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// Runs `operation` with the proof locals that name C values, such as an
/// unfold's named witnesses, in scope for [`synthesize_surface_value`].
pub(in crate::surface) fn with_proof_local_value_names<R>(
    names: Vec<(ProgramValue, SurfaceBinder)>,
    operation: impl FnOnce() -> R,
) -> R {
    struct Restore(Vec<pointer_names::NamedValue>);
    impl Drop for Restore {
        fn drop(&mut self) {
            let previous = std::mem::take(&mut self.0);
            PROOF_LOCAL_VALUE_NAMES.with(|names| *names.borrow_mut() = previous);
        }
    }
    let names = names
        .into_iter()
        .map(pointer_names::NamedValue::new)
        .collect();
    let _restore = Restore(PROOF_LOCAL_VALUE_NAMES.with(|current| current.replace(names)));
    operation()
}

pub(in crate::surface) fn synthesize_surface_value(
    value: &ProgramValue,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Option<SyntaxTerm> {
    if let ProgramValue::Pointer(pointer) = value
        && is_materialized_address(pointer.address())
    {
        return synthesize_materialized_result(pointer.address());
    }
    if matches!(value, ProgramValue::Pointer(pointer) if matches!(pointer.address().base, AddressBase::ContractResult | AddressBase::ContractException | AddressBase::AggregateReturn { .. } | AddressBase::StringLiteral { .. } | AddressBase::AutomaticLocal { .. } | AddressBase::ReferenceCarrier { .. } | AddressBase::StaticObject { .. }))
    {
        return Some(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
            value.clone(),
        )));
    }
    if let Some(name) = pointer_names::native_name(value) {
        return Some(SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
            (name).into(),
        )));
    }
    if let Some(region) = SYNTHESIS_RECORDED_POINTS
        .with(|points| points.borrow().as_ref()?.read_event_naming_value(value))
    {
        return Some(SyntaxTerm::RegionResult(region));
    }
    let _scope = SurfaceSynthesisScope::enter();
    if crate::surface::diagnostics::exact_float_literal_spelling(value).is_some() {
        return Some(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
            value.clone(),
        )));
    }
    match value {
        ProgramValue::Pointer(pointer) if pointer.is_wide() => {
            slices::raise_slice(pointer, parameter_binding, state, &BTreeMap::new())
        }
        ProgramValue::Pointer(pointer) => synthesize_surface_pointer_expression(
            pointer.address(),
            parameter_binding,
            state,
            &BTreeMap::new(),
        ),
        ProgramValue::Int32(term) | ProgramValue::UInt32(term) => {
            synthesize_surface_bitvector(term, parameter_binding, state, &BTreeMap::new())
        }
        _ => None,
    }
}

pub(in crate::surface) fn synthesize_surface_proposition_with_bound_variable_names(
    proposition: &Proposition,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxProposition> {
    let _scope = SurfaceSynthesisScope::enter();
    synthesize_surface_proposition_with_guard_fallback(
        proposition,
        parameter_binding,
        state,
        bound_variables,
    )
}

/// Reconstruct one checked chosen-body leaf. The exact external byte-range
/// spelling is available only at this source-identified projection boundary;
/// ordinary synthesis must not gain a new global search candidate from it.
pub(in crate::surface::proof) fn synthesize_source_projection_proposition_with_bound_variable_names(
    proposition: &Proposition,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxProposition> {
    let _scope = SurfaceSynthesisScope::enter();
    if let Proposition::MemoryLoadable { base, bytes, .. } = proposition {
        match synthesize_exact_external_zero_based_byte_range(
            base,
            bytes.old_form(),
            parameter_binding,
            state,
            bound_variables,
        ) {
            Ok(Some(surface)) => return Some(surface),
            Ok(None) => {}
            Err(()) => return None,
        }
    }
    synthesize_surface_proposition_with_guard_fallback(
        proposition,
        parameter_binding,
        state,
        bound_variables,
    )
}

/// The Surface spelling of `proposition` where each of `names` spells its
/// variable: a proof binder's kernel value.
pub(in crate::surface) fn synthesize_surface_proposition_with_names(
    proposition: &Proposition,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    names: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxProposition> {
    let _scope = SurfaceSynthesisScope::enter();
    synthesize_surface_proposition_with_bound_variables(
        proposition,
        parameter_binding,
        state,
        names,
    )
}

fn synthesize_surface_proposition_with_guard_fallback(
    proposition: &Proposition,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxProposition> {
    let literal = synthesize_surface_proposition_with_bound_variables(
        proposition,
        parameter_binding,
        state,
        bound_variables,
    )?;
    // A proposition body passed with external binder names does not carry
    // enough context to validate a rebuilt Surface candidate independently.
    // The complete quantified proposition still takes the ordinary literal
    // path in that case; this keeps the fallback conservative.
    if !bound_variables.is_empty() {
        return Some(literal);
    }
    let Some(candidate) = omit_leading_definedness_spellings(proposition, &literal) else {
        return Some(literal);
    };
    synthesized_surface_matches_proposition(&candidate, proposition, parameter_binding, state)
        .then_some(candidate)
        .or(Some(literal))
}

#[inline(never)]
fn synthesize_surface_proposition_with_bound_variables(
    proposition: &Proposition,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxProposition> {
    let _frame = SurfaceSynthesisFrame::enter("proposition")?;
    match proposition {
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            let construct: fn(Box<SyntaxProposition>, Box<SyntaxProposition>) -> SyntaxProposition =
                match proposition {
                    Proposition::And(..) => SyntaxProposition::And,
                    Proposition::Or(..) => SyntaxProposition::Or,
                    Proposition::Implies(..) => SyntaxProposition::Implies,
                    _ => unreachable!(),
                };
            let synthesized_left = synthesize_surface_proposition_with_bound_variables(
                left,
                parameter_binding,
                state,
                bound_variables,
            )?;
            let synthesized_right = synthesize_surface_proposition_with_bound_variables(
                right,
                parameter_binding,
                state,
                bound_variables,
            )?;
            Some(construct(
                Box::new(synthesized_left),
                Box::new(synthesized_right),
            ))
        }
        Proposition::ForAll { .. } | Proposition::Exists { .. } => {
            synthesize_surface_quantified_proposition(
                proposition,
                parameter_binding,
                state,
                bound_variables,
            )
        }
        _ => synthesize_surface_atomic_proposition(
            proposition,
            parameter_binding,
            state,
            bound_variables,
        ),
    }
}

/// Whether a kernel conjunction's leading child is the explicit
/// definedness fact generated for a signed C `int32` addition.  The
/// proposition shape, rather than a surface spelling heuristic, identifies
/// the only guard this synthesis fallback may omit.
fn is_leading_add_definedness_guard(proposition: &Proposition) -> bool {
    matches!(
        crate::kernel::proof::arithmetic_special::signed_definedness_query(proposition),
        Some((crate::kernel::SignedDefinedWidth::Int32, _, false))
    )
}

/// Remove only leading Surface spellings of kernel add-definedness guards.
/// The walk follows a quantified wrapper once and strips a contiguous prefix
/// of `And` children, rebuilding each wrapper once on the way back. It does
/// not inspect facts or infer a guard from a convenient-looking expression;
/// the caller validates the one resulting candidate against the complete
/// kernel proposition.
fn omit_leading_definedness_spellings(
    proposition: &Proposition,
    surface: &SyntaxProposition,
) -> Option<SyntaxProposition> {
    match (proposition, surface) {
        (
            Proposition::ForAll { body, .. },
            SyntaxProposition::ForAll {
                body: surface_body, ..
            },
        ) => {
            let body = omit_leading_definedness_spellings(body, surface_body)?;
            let SyntaxProposition::ForAll {
                click_type, name, ..
            } = surface
            else {
                unreachable!("surface universal matched above");
            };
            Some(SyntaxProposition::ForAll {
                click_type: click_type.clone(),
                name: name.clone(),
                written_name: None,
                body: Box::new(body),
            })
        }
        (
            Proposition::Exists { body, .. },
            SyntaxProposition::Exists {
                body: surface_body, ..
            },
        ) => {
            let body = omit_leading_definedness_spellings(body, surface_body)?;
            let SyntaxProposition::Exists {
                click_type, name, ..
            } = surface
            else {
                unreachable!("surface existential matched above");
            };
            Some(SyntaxProposition::Exists {
                click_type: click_type.clone(),
                name: name.clone(),
                written_name: None,
                body: Box::new(body),
            })
        }
        (Proposition::And(_, _), SyntaxProposition::And(_, _)) => {
            let mut proposition = proposition;
            let mut surface = surface;
            let mut omitted = false;
            while let Proposition::And(left, right) = proposition {
                if !is_leading_add_definedness_guard(left)
                    || !matches!(surface, SyntaxProposition::And(..))
                {
                    break;
                }
                let SyntaxProposition::And(_, surface_right) = surface else {
                    unreachable!("surface conjunction matched above");
                };
                proposition = right;
                surface = surface_right;
                omitted = true;
            }
            omitted.then(|| surface.clone())
        }
        _ => None,
    }
}

/// Re-lower one candidate through the ordinary fixed-state path and require
/// the complete proposition to retain its shared alpha/load identity.  This
/// is intentionally a small, context-free validation used only for the
/// arithmetic guard fallback; callers with state- or proof-local context
/// still perform their own authoritative re-lowering.
fn synthesized_surface_matches_proposition(
    candidate: &SyntaxProposition,
    proposition: &Proposition,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> bool {
    // A retained call requirement may carry a caller variable as the
    // selected pointer argument. The normal contract environment builder
    // expects already-evaluated call values, so resolve only this exact
    // pointer variable through the current state's indexed local binding for
    // the round-trip check. Other expressions remain rejected.
    let resolved_arguments = parameter_binding
        .arguments
        .iter()
        .map(|argument| match argument {
            ProgramExpression::Variable(name) => match state.locals().get(name) {
                Some(value) if value.pointer().is_some() => {
                    ProgramExpression::Value(value.clone().into_native())
                }
                _ => argument.clone(),
            },
            _ => argument.clone(),
        })
        .collect::<Vec<_>>();
    let Ok(parameter_values) = parameter_values(ParameterBinding::new(
        parameter_binding.parameters,
        &resolved_arguments,
    )) else {
        return false;
    };
    let array_refs = array_refs_for_parameters(
        parameter_binding.parameters,
        &parameter_values,
        &state.program_point(),
    );
    let (values, array_refs) = contract_environment_at_state(&parameter_values, &array_refs, state);
    let pointer_element_widths =
        crate::surface::lowering::parameter_pointer_element_widths(parameter_binding.parameters);
    let lowered = super::execution_planning::without_open_obligation_probe(|| {
        crate::surface::proof::fixed_state_proofs::lower_fixed_state_proposition_through_kernel_with(
            candidate,
            &PureFactContext::new(),
            ContractEnvironment::new(&values, &array_refs).with_parameters(parameter_binding),
            FixedStateFrame::new(state, state, None, &RecordedStates::default()),
            SpecDefinitions::new(
                &PredicateEnvironment::new(&[]),
                &ClickFunctionEnvironment::new(&[]),
            ),
            FixedStateLoweringOptions {
                pointer_element_widths,
                ..Default::default()
            },
        )
    });
    lowered.is_ok_and(|lowered| {
        crate::kernel::proof::propositions_are_alpha_equal(&lowered, proposition)
    })
}

#[inline(never)]
fn synthesize_surface_quantified_proposition(
    proposition: &Proposition,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxProposition> {
    match proposition {
        Proposition::ForAll {
            var, sort, body, ..
        }
        | Proposition::Exists {
            var, sort, body, ..
        } => {
            // A machine integer binder, or a slice binder, which names its
            // slice, its data pointer and its count
            // (`design/rust-slice-values.md`, step 2b-iii-b-i).
            let slice_element = match sort.pointer_type() {
                Some(ProgramType::SlicePointer(element)) => Some(element),
                _ => None,
            };
            let binder_type = match slice_element {
                Some(element) => ProgramType::SlicePointer(element),
                None => sort.machine_integer_type()?.program_type(),
            };
            let click_type = ClickType::Program(
                crate::surface::generics::interface_type_from_program_type(binder_type),
            );
            // The binder keeps the name it was written with when nothing the
            // body can name is spelled the same; otherwise a generated
            // binder, which never captures a source name.
            let written = match proposition {
                Proposition::ForAll { name, .. } => name.as_str(),
                Proposition::Exists { name, .. } => Some(name.as_str()),
                _ => None,
            }
            .filter(|name| {
                quantifier_name_is_free(name, parameter_binding, state, bound_variables)
            });
            let name = written
                .map(|name| SurfaceBinder::Written(name.to_string()))
                .unwrap_or_else(SurfaceBinder::fresh);
            let _binder =
                folds::Binding::enter((folds::BinderCarrier::Program, **var), name.clone());
            let _slice_binder =
                slice_element.map(|element| folds::SliceBinding::enter(**var, element));
            let body = Box::new(synthesize_surface_proposition_with_bound_variables(
                body,
                parameter_binding,
                state,
                bound_variables,
            )?);
            Some(match proposition {
                Proposition::ForAll { .. } => SyntaxProposition::ForAll {
                    click_type: click_type.clone(),
                    name,
                    written_name: None,
                    body,
                },
                Proposition::Exists { .. } => SyntaxProposition::Exists {
                    click_type: click_type.clone(),
                    name,
                    written_name: None,
                    body,
                },
                _ => unreachable!(),
            })
        }
        _ => unreachable!("non-quantified proposition dispatched to binder synthesis"),
    }
}

/// Whether a quantifier written `name` can keep that name when raised: no
/// parameter, local, given or proof binder, or enclosing binder is spelled
/// the same, so the new binder shadows nothing its body names.
fn quantifier_name_is_free(
    name: &str,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> bool {
    !name.is_empty()
        && !name.starts_with("__")
        && !parameter_binding
            .parameters
            .iter()
            .any(|parameter| parameter.name() == name)
        && state.locals().get(name).is_none()
        && !bound_variables
            .values()
            .any(|binder| binder.written() == Some(name))
        && !PROOF_BINDER_NAMES.with(|names| {
            names
                .borrow()
                .values()
                .any(|binder| binder.written() == Some(name))
        })
        && !folds::written_name_in_scope(name)
}

/// `loadable(<base>[0..n])`: the whole named region, its byte count a
/// multiple of the `int32` cell the segment counts in. The start index is
/// zero, so the pointer's own offset is folded into the printed base.
fn synthesize_zero_based_loadable_segment(
    base: &Address,
    bytes: &OldMachineTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxProposition> {
    // A displaced pointer may encode the start of a named range. Prefer that
    // faithful spelling when a folded byte count still identifies the named
    // pointer; otherwise retain the ordinary zero-based fallback for pointer
    // expressions whose offset has no recoverable written range.
    if bytes.as_const().is_some()
        && let Some(named) = synthesize_named_range_loadable_segment(
            base,
            bytes,
            parameter_binding,
            state,
            bound_variables,
        )
    {
        return Some(named);
    }
    let (element_count, element_pointer_type) = if let Some(byte_count) = bytes.as_const() {
        // A count that is not a whole number of four-byte units is a byte
        // span, spelled over the base viewed as bytes.
        if !byte_count.is_multiple_of(4) {
            (
                ProgramExpression::Value(int32(byte_count)),
                ProgramType::UInt8Pointer,
            )
        } else {
            (
                ProgramExpression::Value(int32(byte_count / 4)),
                ProgramType::Int32Pointer,
            )
        }
    } else if let binary_term!(Int32, Multiply, left, right) = bytes {
        let elements = if right.as_const() == Some(4) {
            left.as_ref()
        } else if left.as_const() == Some(4) {
            right.as_ref()
        } else {
            return None;
        };
        // A scaled difference is the byte count of a written named range.
        // Its nonzero start must remain in the surface spelling; treating the
        // difference as a zero-based element count would lose that endpoint
        // and can accidentally attribute it to an unrelated index.
        if let binary_term!(Int32, Subtract, _, start) = elements
            && start.as_const() != Some(0)
        {
            return None;
        }
        (
            contract_expression_to_program_expression(&synthesize_surface_bitvector(
                elements,
                parameter_binding,
                state,
                bound_variables,
            )?)?,
            ProgramType::Int32Pointer,
        )
    } else if !matches!(bytes, binary_term!(Int32, Subtract, _, _)) {
        // A byte span remains unscaled over an explicit byte pointer.
        (
            contract_expression_to_program_expression(&synthesize_surface_bitvector(
                bytes,
                parameter_binding,
                state,
                bound_variables,
            )?)?,
            ProgramType::UInt8Pointer,
        )
    } else {
        return None;
    };
    let semantic_base = synthesize_surface_pointer(base, parameter_binding, state, bound_variables);
    // These counts use scalar units, regardless of the named pointer's
    // pointee (including a struct-valued proof binder). Spell those units
    // explicitly instead of relying on its historical four-byte carrier.
    let semantic_base = ProgramExpression::Cast {
        expression: Box::new(semantic_base?),
        target_type: element_pointer_type,
        integer_mode: crate::kernel::IntegerCastMode::Standard,
        pointee_struct: None,
        pointee_struct_size: None,
        pointee_volatile: false,
        pointee_constant: false,
        explicit_qualification: false,
    };
    let surface_base = SyntaxTerm::ProgramExpression(semantic_base.clone());
    Some(SyntaxProposition::Loadable {
        segment: ContractSegment {
            uninitialized: false,
            state: ContractSegmentState::Current,
            base: semantic_base,
            start: ProgramExpression::Value(int32(0)),
            end: element_count.clone(),
            surface: ContractSegmentSurface::Range {
                base: surface_base,
                start: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
                end: SyntaxTerm::ProgramExpression(element_count),
            },
        },
    })
}

/// `loadable(bytes[0..n])` for one exact external byte-pointer parameter.
///
/// External argument pointers may carry a symbolic allocation offset, so the
/// general pointer synthesizer cannot treat that offset as a range index. If
/// the load starts at the exact pointer value supplied for a declared byte
/// parameter, the byte count is already the written element count. Require a
/// unique exact parameter match: an aliased parameter is not enough source
/// information to choose one spelling over another.
fn synthesize_exact_external_zero_based_byte_range(
    base: &Address,
    bytes: &OldMachineTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Result<Option<SyntaxProposition>, ()> {
    if base.base != AddressBase::ExternalArgument {
        return Ok(None);
    }
    let mut matches = parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
        .filter_map(|(parameter, argument)| {
            if parameter
                .interface_type()
                .pointee_type()?
                .to_kernel_type()
                .byte_width()
                != 1
            {
                return None;
            }
            let pointer = match argument {
                ProgramExpression::Value(ProgramValue::Pointer(pointer)) => pointer,
                ProgramExpression::Variable(name) => state.locals().get(name)?.pointer()?,
                _ => return None,
            };
            (pointer.address() == base && pointer.program_type().pointee_type()?.byte_width() == 1)
                .then(|| crate::surface::surface_parameter_binding(parameter.binding_name()))
        });
    let Some(name) = matches.next() else {
        return Ok(None);
    };
    if matches.next().is_some() {
        return Err(());
    }
    let end = synthesize_surface_bitvector(bytes, parameter_binding, state, bound_variables)
        .and_then(|end| contract_expression_to_program_expression(&end))
        .ok_or(())?;
    let named = ProgramExpression::Variable(name);
    let start = ProgramExpression::Value(int32(0));
    Ok(Some(SyntaxProposition::Loadable {
        segment: ContractSegment {
            uninitialized: false,
            state: ContractSegmentState::Current,
            base: named.clone(),
            start: start.clone(),
            end: end.clone(),
            surface: ContractSegmentSurface::Range {
                base: SyntaxTerm::ProgramExpression(named),
                start: SyntaxTerm::ProgramExpression(start),
                end: SyntaxTerm::ProgramExpression(end),
            },
        },
    }))
}

/// `loadable(p[a..b])`: a range of one named pointer, the form a contract
/// writes when neither end of the range is the object's own start.
///
/// A call requirement lowered from such a clause keeps the written ends: its
/// byte count is `(b - a)` scaled by the element, and its base pointer is
/// `p` displaced by `a` elements. Both survive only if the range is spelled
/// back over the same named pointer, so this reads `a` out of the pointer
/// offset rather than folding it into the base as the zero-based form does.
/// A spelling whose ends differ re-lowers to a different byte count, which
/// is exactly what the caller's round-trip check rejects.
fn synthesize_named_range_loadable_segment(
    base: &Address,
    bytes: &OldMachineTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxProposition> {
    if let Some(segment) = synthesize_struct_loadable_segment(base, bytes, parameter_binding, state)
    {
        return Some(segment);
    }
    // A one-element byte range is either the producer's folded representation
    // of `bytes[index..index + 1]` or its exact constant byte count. Handle it
    // before the historical folded-range paths so the source index comes from
    // the exact external parameter displacement rather than a same-block
    // inference.
    if base.base == AddressBase::ExternalArgument
        && is_one_element_byte_count(bytes)
        && let Some(special) = synthesize_external_symbolic_element_range(
            base,
            bytes,
            parameter_binding,
            state,
            bound_variables,
        )
    {
        return Some(special);
    }
    let named_pointer_state =
        if base.base == AddressBase::ExternalArgument && is_reduced_one_element_byte_count(bytes) {
            None
        } else {
            Some(state)
        };
    if let Some(byte_count) = bytes.as_const() {
        let (named, width, start) =
            named_range_bases(parameter_binding, named_pointer_state, state)
                .into_iter()
                .filter_map(|named| {
                    if matches!(named.pointer.offset.view(), OffsetView::Constant(0))
                        || byte_count % named.width != 0
                    {
                        return None;
                    }
                    let start =
                        base.element_index_from_base_with_width(&named.pointer, named.width)?;
                    let width = named.width;
                    Some((named, width, start))
                })
                .find(|(_, _, start)| start.as_const().is_some_and(|start| start != 0))?;
        let element_count = byte_count / width;
        let end = OldMachineTerm::add(start.clone(), OldMachineTerm::constant(element_count));
        let start = contract_expression_to_program_expression(&synthesize_surface_bitvector(
            &start,
            parameter_binding,
            state,
            bound_variables,
        )?)?;
        let end = contract_expression_to_program_expression(&synthesize_surface_bitvector(
            &end,
            parameter_binding,
            state,
            bound_variables,
        )?)?;
        return Some(SyntaxProposition::Loadable {
            segment: ContractSegment {
                uninitialized: false,
                state: ContractSegmentState::Current,
                base: named.lowered,
                start: start.clone(),
                end: end.clone(),
                surface: ContractSegmentSurface::Range {
                    base: named.surface,
                    start: SyntaxTerm::ProgramExpression(start),
                    end: SyntaxTerm::ProgramExpression(end),
                },
            },
        });
    }
    // The byte count as the segment lowering builds it: the element span,
    // scaled by the element width when that is not one byte.
    let (span, scale) = match bytes {
        binary_term!(Int32, Multiply, left, right) => match (left.as_const(), right.as_const()) {
            (_, Some(scale)) => (left.as_ref(), scale),
            (Some(scale), _) => (right.as_ref(), scale),
            _ => return None,
        },
        span => (span, 1),
    };
    let binary_term!(Int32, Subtract, end, start) = span else {
        return None;
    };
    // The named pointer this range starts from, and the element index the
    // requirement's base pointer sits at within it.
    let named = named_range_bases(parameter_binding, named_pointer_state, state)
        .into_iter()
        .find(|named| {
            named.width == scale
                && base
                    .element_index_from_base_with_width(&named.pointer, named.width)
                    .is_some_and(|index| index == **start)
        })?;
    let start = contract_expression_to_program_expression(&synthesize_surface_bitvector(
        start,
        parameter_binding,
        state,
        bound_variables,
    )?)?;
    let end = contract_expression_to_program_expression(&synthesize_surface_bitvector(
        end,
        parameter_binding,
        state,
        bound_variables,
    )?)?;
    Some(SyntaxProposition::Loadable {
        segment: ContractSegment {
            uninitialized: false,
            state: ContractSegmentState::Current,
            base: named.lowered,
            start: start.clone(),
            end: end.clone(),
            surface: ContractSegmentSurface::Range {
                base: named.surface,
                start: SyntaxTerm::ProgramExpression(start),
                end: SyntaxTerm::ProgramExpression(end),
            },
        },
    })
}

/// Recover the written range for a one-element byte load emitted by
/// `loadable(bytes[index..index + 1])`. This is deliberately narrower than
/// `Address::element_index_from_base_with_width`: only a declared external
/// parameter, an exact direct displacement from that parameter's pointer, and
/// a one-byte element are authoritative enough to reconstruct the spelling.
/// The producer may retain either the exact constant `1` or the unreduced
/// `(index + 1) - index` form.
fn synthesize_external_symbolic_element_range(
    base: &Address,
    bytes: &OldMachineTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxProposition> {
    let (name, index) = parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
        .find_map(|(parameter, argument)| {
            let named_base = match argument {
                ProgramExpression::Value(ProgramValue::Pointer(pointer)) => pointer,
                // Call-site arguments normally have already been evaluated
                // to values, but a retained call requirement can carry the
                // caller's exact variable expression instead. Resolve only
                // that selected name through the current state's indexed
                // local binding; do not infer a pointer from ambient facts.
                ProgramExpression::Variable(name) => state.locals().get(name)?.pointer()?,
                _ => return None,
            };
            if parameter
                .interface_type()
                .pointee_type()?
                .to_kernel_type()
                .byte_width()
                != 1
                || named_base.program_type().pointee_type()?.byte_width() != 1
                || named_base.address().base != AddressBase::ExternalArgument
                || base.base != AddressBase::ExternalArgument
            {
                return None;
            }
            let index = match base.offset.view() {
                OffsetView::Add(left, right) if left == &named_base.address().offset => {
                    int32_scaled_value(right, 1)?
                }
                OffsetView::Add(left, right) if right == &named_base.address().offset => {
                    int32_scaled_value(left, 1)?
                }
                // `bytes` itself can be at offset zero, in which case the
                // canonical pointer offset drops the zero-valued add.
                _ if matches!(named_base.address().offset.view(), OffsetView::Constant(0)) => {
                    int32_scaled_value(&base.offset, 1)?
                }
                _ => return None,
            };
            let one_element = binary_node!(
                Int32,
                Subtract,
                Box::new(OldMachineTerm::add(
                    index.clone(),
                    OldMachineTerm::constant(1),
                )),
                Box::new(index.clone()),
            );
            if !matches!(bytes, bits32_constant!(1)) && bytes != &one_element {
                return None;
            }
            (!matches!(index, bits32_constant!(_))).then_some((
                crate::surface::surface_parameter_binding(parameter.binding_name()),
                index,
            ))
        })?;
    if matches!(bytes, bits32_constant!(1)) {
        // Keep the byte count constant in the re-lowered proposition by
        // moving the symbolic index into the named pointer expression and
        // spelling a zero-based one-byte range over that displaced pointer.
        let semantic_base =
            synthesize_surface_pointer(base, parameter_binding, state, bound_variables)?;
        let surface_base = SyntaxTerm::ProgramExpression(semantic_base.clone());
        let start = ProgramExpression::Value(int32(0));
        let end = ProgramExpression::Value(int32(1));
        return Some(SyntaxProposition::Loadable {
            segment: ContractSegment {
                uninitialized: false,
                state: ContractSegmentState::Current,
                base: semantic_base,
                start: start.clone(),
                end: end.clone(),
                surface: ContractSegmentSurface::Range {
                    base: surface_base,
                    start: SyntaxTerm::ProgramExpression(start),
                    end: SyntaxTerm::ProgramExpression(end),
                },
            },
        });
    }
    let start = contract_expression_to_program_expression(&synthesize_surface_bitvector(
        &index,
        parameter_binding,
        state,
        bound_variables,
    )?)?;
    let end_term = OldMachineTerm::add(index, OldMachineTerm::constant(1));
    let end = contract_expression_to_program_expression(&synthesize_surface_bitvector(
        &end_term,
        parameter_binding,
        state,
        bound_variables,
    )?)?;
    let named = ProgramExpression::Variable(surface_local_name(name));
    Some(SyntaxProposition::Loadable {
        segment: ContractSegment {
            uninitialized: false,
            state: ContractSegmentState::Current,
            base: named.clone(),
            start: start.clone(),
            end: end.clone(),
            surface: ContractSegmentSurface::Range {
                base: SyntaxTerm::ProgramExpression(named),
                start: SyntaxTerm::ProgramExpression(start),
                end: SyntaxTerm::ProgramExpression(end),
            },
        },
    })
}

fn is_reduced_one_element_byte_count(bytes: &OldMachineTerm) -> bool {
    let binary_term!(Int32, Subtract, end, start) = bytes else {
        return false;
    };
    *end.as_ref() == OldMachineTerm::add(start.as_ref().clone(), OldMachineTerm::constant(1))
}

fn is_one_element_byte_count(bytes: &OldMachineTerm) -> bool {
    matches!(bytes, bits32_constant!(1)) || is_reduced_one_element_byte_count(bytes)
}

fn int32_scaled_value(offset: &AddressOffset, width: i64) -> Option<OldMachineTerm> {
    match offset.view() {
        OffsetView::Int32Scaled { index, byte_width } if byte_width == width => {
            Some(index.structural_value().clone())
        }
        _ => None,
    }
}

/// Every pointer this proof context can name, with the element width its
/// declared type steps by: the call's own parameters first, then the state's
/// pointer locals. The walk is over those two named lists only.
/// The pointers parameters and locals name, each with its element width: a
/// pointer itself, or a Rust slice's data pointer, `s.as_ptr()`
/// (`design/rust-slice-values.md`, step 3b).
fn named_pointer_bases<'a>(
    parameter_binding: ParameterBinding<'a>,
    state: Option<&'a ExecutionState>,
) -> impl Iterator<Item = (ProgramExpression, crate::kernel::Pointer, u32)> + 'a {
    let named = |name: crate::kernel::BindingName, base: &crate::kernel::Pointer| {
        let name = ProgramExpression::Variable(name);
        if base.is_wide() {
            let crate::kernel::ProgramType::SlicePointer(element) = base.program_type() else {
                return None;
            };
            let width = element.thin_pointer_type().pointee_type()?.byte_width();
            return Some((
                ProgramExpression::SliceData(Box::new(name)),
                base.as_ptr(),
                width,
            ));
        }
        let width = base.program_type().pointee_type()?.byte_width();
        Some((name, base.clone(), width))
    };
    parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
        .filter_map(move |(parameter, argument)| {
            let ProgramExpression::Value(ProgramValue::Pointer(base)) = argument else {
                return None;
            };
            let name = crate::surface::surface_parameter_binding(parameter.binding_name());
            if base.is_wide() {
                return named(name, base);
            }
            let width = parameter
                .interface_type()
                .pointee_type()?
                .to_kernel_type()
                .byte_width();
            Some((ProgramExpression::Variable(name), base.clone(), width))
        })
        .chain(state.into_iter().flat_map(move |state| {
            state
                .locals()
                .object_values()
                .filter_map(move |(name, value)| {
                    value.pointer()?;
                    let native = value.native();
                    let ProgramValue::Pointer(base) = native.as_ref() else {
                        return None;
                    };
                    named(surface_local_name(name), base)
                })
        }))
}

/// Synthesize the internal equation emitted when a memory read is assigned a
/// registered load identity. The variable is not a source-level identifier;
/// spell both sides through the registered pointer, anchored at the state
/// named by the load.  Keeping this separate from ordinary bitvector
/// synthesis is important: the latter may deliberately resolve a load to a
/// current-state value, while this equation must retain its memory version.
fn synthesize_load_defining_equation(
    variable: &Variable,
    memory: &crate::kernel::SharedMemory,
    pointer: &Address,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxProposition> {
    let (registered_memory, registered_pointer) =
        crate::kernel::registered_load_for_variable(variable)?;
    // The defining equation carries the canonical state that was recorded
    // with this variable. A merely equivalent load from another memory would
    // erase the epoch the equation is required to preserve.
    if registered_memory != *memory || registered_pointer != *pointer {
        return None;
    }

    let synthesize_at = |retained_state: &ExecutionState| {
        let load = registered_load_in_state(variable, retained_state)?;
        // Let the ordinary load spelling select a qualified source, an exact
        // local cell, a field, or the pointer/load fallback. It receives the
        // state-specific load above, so the selected source cannot drift
        // to another epoch while the defining equation is presented.
        let left = synthesize_surface_bitvector(
            &OldMachineTerm::Variable(*variable),
            parameter_binding,
            retained_state,
            bound_variables,
        )?;
        let right = synthesize_surface_bitvector(
            &load,
            parameter_binding,
            retained_state,
            bound_variables,
        )?;
        Some(SyntaxProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            right,
        })
    };

    if registered_load_in_state(variable, state).is_some() {
        return synthesize_at(state);
    }
    if let Some(entry) = SYNTHESIS_ENTRY_STATE.with(|slot| slot.borrow().clone())
        && registered_load_in_state(variable, &entry).is_some()
    {
        return synthesize_at(&entry).map(|proposition| SyntaxProposition::At {
            selector: ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Function,
                kind: ProgramPointKind::Entry,
            }),
            proposition: Box::new(proposition),
        });
    }
    SYNTHESIS_REFERENCE_STATE
        .with(|slot| {
            let slot = slot.borrow();
            let (retained_state, selector) = slot.as_ref()?;
            registered_load_in_state(variable, retained_state)?;
            synthesize_at(retained_state).map(|proposition| SyntaxProposition::At {
                selector: selector.clone(),
                proposition: Box::new(proposition),
            })
        })
        .or_else(|| {
            let read = crate::kernel::registered_load_term_for_variable(variable)?;
            let (selector, retained_state, _) = recorded_point_of_load(&read)?;
            synthesize_at(&retained_state).map(|proposition| SyntaxProposition::At {
                selector,
                proposition: Box::new(proposition),
            })
        })
}

/// The canonical Boolean cell read is an unsigned byte tested against zero.
/// Use its Boolean load spelling when the read's memory identifies a Boolean
/// object. The same comparison over arbitrary bytes keeps its comparison
/// spelling, since it can be valid where a typed Boolean access is refused.
fn synthesize_boolean_cell_read(
    zero_test: crate::kernel::BooleanOperandView<'_>,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let (MachineIntegerType::UInt8, CompareRelation::Equal, [left, right]) =
        zero_test.comparison()?
    else {
        return None;
    };
    if right.literal()?.bool_constant_value() != Some(false) {
        return None;
    }
    let read = left.read_source()?;
    let OldMachineTerm::MemoryLoad(point, address, crate::kernel::LoadKind::UInt8) = read.as_ref()
    else {
        return None;
    };
    if point.read_version_id().is_some() {
        if point.memory().has_boolean_cell_type(address) {
            return synthesize_point_read(
                point,
                address,
                ProgramType::Bool,
                parameter_binding,
                state,
                bound_variables,
            );
        }
        return None;
    }
    if !point.memory().has_boolean_cell_type(address) {
        return None;
    }
    // A snapshot read can use a typed Boolean spelling only where lowering
    // still uses a detached view. A certified point gives the spelling its
    // own point-keyed read.
    let selects_read = |state: &ExecutionState| {
        &crate::kernel::intern_memory_ref(state.memory()) == point.shared_memory()
            && !state.program_point().has_certified_read_view()
    };
    let expression = |state: &ExecutionState| {
        Some(synthesize_typed_load(
            synthesize_surface_pointer_expression(
                address,
                parameter_binding,
                state,
                bound_variables,
            )?,
            ProgramType::Bool,
        ))
    };
    if selects_read(state) {
        return expression(state);
    }
    if let Some(entry) = SYNTHESIS_ENTRY_STATE.with(|slot| slot.borrow().clone())
        && selects_read(&entry)
    {
        return Some(SyntaxTerm::Old(Box::new(expression(&entry)?)));
    }
    SYNTHESIS_RECORDED_POINTS.with(|slot| {
        let slot = slot.borrow();
        let (selector, recorded) = slot.as_ref()?.point_reading_memory(point.shared_memory())?;
        selects_read(recorded).then_some(())?;
        Some(SyntaxTerm::At {
            selector: selector.clone(),
            expression: Box::new(expression(recorded)?),
        })
    })
}

// Large leaf temporaries must not occupy every recursive connective frame.
#[inline(never)]
/// Spell a logical Bool by its structure, including Bool operands of calls.
fn synthesize_surface_bool(
    condition: &OldConditionTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let _frame = SurfaceSynthesisFrame::enter("bool")?;
    crate::instrumentation::record_deterministic_work(1);
    if let Some(zero_test) = condition.bool_negation_operand()
        && let Some(read) = synthesize_boolean_cell_read(
            crate::kernel::BooleanOperandView::Native(zero_test),
            parameter_binding,
            state,
            bound_variables,
        )
    {
        return Some(read);
    }
    let operand = |condition: &OldConditionTerm| {
        synthesize_surface_bool(condition, parameter_binding, state, bound_variables)
    };
    match condition {
        OldConditionTerm::Constant(value) => Some(bool_literal(*value)),
        OldConditionTerm::Variable(variable) => {
            if let Some(name) = folds::binder_name(false, *variable)
                .or_else(|| bound_variables.get(variable).cloned())
            {
                return Some(name.reference());
            }
            synthesize_surface_bitvector(
                &OldMachineTerm::bool_cast(MachineIntegerType::UInt8, condition.clone()),
                parameter_binding,
                state,
                bound_variables,
            )
        }
        OldConditionTerm::BoolApplication(application) => synthesize_surface_call(
            application.name(),
            application.arguments(),
            parameter_binding,
            state,
            bound_variables,
        ),
        OldConditionTerm::BoolIf {
            condition,
            then_condition,
            else_condition,
        } => Some(SyntaxTerm::If {
            condition: Box::new(bool_truth(operand(condition)?)),
            then_branch: Box::new(operand(then_condition)?),
            else_branch: Box::new(operand(else_condition)?),
        }),
        OldConditionTerm::Float32(_) | OldConditionTerm::Float64(_) => raise_kernel_term(
            &crate::kernel::KernelTermImport::default().condition(condition),
            parameter_binding,
            state,
            bound_variables,
        ),
        OldConditionTerm::BoolEqual(left, right) => {
            proposition_bool_value(SyntaxProposition::Comparison {
                left: operand(left)?,
                operator: ComparisonOperator::Equal,
                right: operand(right)?,
            })
            .ok()
        }
        _ => proposition_bool_value(synthesize_surface_atomic_proposition(
            &Proposition::condition_is(condition.clone(), true),
            parameter_binding,
            state,
            bound_variables,
        )?)
        .ok(),
    }
}

/// Whether `expression` reads a `bool` local of `state`, or reads one at a
/// recorded point.
fn names_bool_local(expression: &SyntaxTerm, state: &ExecutionState) -> bool {
    match expression {
        SyntaxTerm::ProgramExpression(ProgramExpression::Variable(name)) => state
            .locals()
            .get(name)
            .is_some_and(|value| value.program_type() == ProgramType::Bool),
        SyntaxTerm::ProgramBinding(name) => state
            .locals()
            .get(name)
            .is_some_and(|value| value.program_type() == ProgramType::Bool),
        SyntaxTerm::At { expression, .. } => names_bool_local(expression, state),
        _ => false,
    }
}

fn synthesize_surface_atomic_proposition(
    proposition: &Proposition,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxProposition> {
    if let Proposition::ConditionIs(condition, zero) = proposition
        && let Some(read) = synthesize_boolean_cell_read(
            condition.operand_view(),
            parameter_binding,
            state,
            bound_variables,
        )
    {
        return Some(SyntaxProposition::Comparison {
            left: read,
            operator: ComparisonOperator::Equal,
            right: bool_literal(!*zero),
        });
    }
    if let Proposition::ConditionIs(condition, value) = proposition
        && let Some(root) = condition.root()
    {
        use crate::kernel::KernelTermNode as Node;
        let raise = |term| raise_kernel_term(term, parameter_binding, state, bound_variables);
        let equality = if *value {
            ComparisonOperator::Equal
        } else {
            ComparisonOperator::NotEqual
        };
        match root.node() {
            Node::AlgebraicEqual {
                arguments: [left, right],
            } => {
                return Some(SyntaxProposition::Comparison {
                    left: raise(left)?,
                    operator: equality,
                    right: raise(right)?,
                });
            }
            Node::BoolEqual {
                arguments: [left, right],
            } if let (Node::BoolLiteral(left), Node::BoolLiteral(right)) =
                (left.node(), right.node()) =>
            {
                return Some(SyntaxProposition::Comparison {
                    left: bool_literal(*left),
                    operator: equality,
                    right: bool_literal(*right),
                });
            }
            Node::Variable(_)
            | Node::Call { .. }
            | Node::BoolIf { .. }
            | Node::BoolEqual { .. } => {
                let claim = bool_truth(raise(root)?);
                return Some(if *value {
                    claim
                } else {
                    SyntaxProposition::Not(Box::new(claim))
                });
            }
            _ => {}
        }
    }
    if let Proposition::ConditionIs(condition, value) = proposition
        && let Some((operator, operands)) =
            crate::kernel::machine_integer::comparison::written_integer_comparison(
                condition.operand_view(),
            )
    {
        return raise_integer_comparison(
            operator,
            &operands,
            *value,
            parameter_binding,
            state,
            bound_variables,
        );
    }
    // A `bool` local's truth, C's test `w != 0` at `uint8` of its carrier:
    // the claim on the local, `w` or `not w`, which is what a claim on it
    // lowers to. Compared with an integer, as `w != 0`, it would not lower.
    if let Some((
        OldConditionTerm::Compare {
            format: MachineIntegerType::UInt8,
            relation: CompareRelation::Equal,
            left,
            right,
        },
        value,
    )) = (proposition).old_condition()
        && right.bool_constant_value() == Some(false)
        && let Some(word) =
            synthesize_surface_bitvector(left, parameter_binding, state, bound_variables)
        && names_bool_local(&word, state)
    {
        let claim = crate::surface::bool_truth(word);
        return Some(if *value {
            SyntaxProposition::Not(Box::new(claim))
        } else {
            claim
        });
    }
    if let Some((
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        },
        true,
    )) = (proposition).old_condition()
        && let (
            OldMachineTerm::Variable(variable),
            OldMachineTerm::MemoryLoad(memory, pointer, kind),
        ) = (left.as_ref(), right.as_ref())
        && crate::kernel::is_load_variable(variable)
        && crate::kernel::registered_load_kind_for_variable(variable) == Some(*kind)
    {
        return synthesize_load_defining_equation(
            variable,
            memory.shared_memory(),
            pointer,
            parameter_binding,
            state,
            bound_variables,
        );
    }
    if let Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) = proposition {
        let raise = |value: &crate::kernel::StoredAlgebraicTerm| match value.root() {
            Some(root) => raise_kernel_term(root, parameter_binding, state, bound_variables),
            None => synthesize_surface_algebraic(
                value.old_form(),
                parameter_binding,
                state,
                bound_variables,
            ),
        };
        return Some(SyntaxProposition::Comparison {
            left: raise(left)?,
            operator: ComparisonOperator::Equal,
            right: raise(right)?,
        });
    }
    if let Proposition::Equal(Term::Sequence(left), Term::Sequence(right)) = proposition {
        return Some(SyntaxProposition::Comparison {
            left: synthesize_surface_sequence(left, parameter_binding, state, bound_variables)?,
            operator: ComparisonOperator::Equal,
            right: synthesize_surface_sequence(right, parameter_binding, state, bound_variables)?,
        });
    }
    if let Proposition::SequenceMembership { element, sequence } = proposition {
        return Some(SyntaxProposition::Comparison {
            left: synthesize_surface_sequence_element(
                element.old_form(),
                parameter_binding,
                state,
                bound_variables,
            )?,
            operator: ComparisonOperator::In,
            right: synthesize_surface_sequence(
                sequence,
                parameter_binding,
                state,
                bound_variables,
            )?,
        });
    }
    // The hidden resource-state argument has no written spelling. A
    // predicate's array source point is followed by its pointer, so each
    // argument can be raised at its own recorded point.
    if let Proposition::Predicate {
        name,
        arguments: kernel_arguments,
    } = proposition
    {
        if let Some(surface) = super::program_termination::predicate_spelling(name) {
            return Some(surface);
        }
        // Type evidence about a pointer is `is_a<T>(p)`. Its class is the one
        // the pointer's evidence carries, and names this exact fact.
        if crate::kernel::is_object_type_predicate_name(name) {
            let [argument] = kernel_arguments.as_slice() else {
                return None;
            };
            let Some(ProgramValue::Pointer(pointer)) = argument.program_value_native() else {
                return None;
            };
            let class = pointer.object_class()?;
            if crate::kernel::object_type_predicate_name(&class) != *name {
                return None;
            }
            return Some(SyntaxProposition::IsA {
                class,
                pointer: synthesize_surface_pointer_expression(
                    pointer,
                    parameter_binding,
                    state,
                    bound_variables,
                )?,
            });
        }
        let mut call_arguments = Vec::new();
        let mut index = usize::from(matches!(
            kernel_arguments.first(),
            Some(Term::ExecutionState(_))
        ));
        while index < kernel_arguments.len() {
            match &kernel_arguments[index] {
                Term::ArrayReadPoint(point) => {
                    let Some(term_source_0 @ Term::ProgramValue(_)) =
                        kernel_arguments.get(index + 1)
                    else {
                        return None;
                    };
                    let (Some(ProgramValue::Pointer(pointer)),) =
                        (term_source_0.program_value_native(),)
                    else {
                        return None;
                    };
                    call_arguments.push(synthesize_at_read_origin(point, state, |selected| {
                        synthesize_surface_pointer_expression(
                            pointer,
                            parameter_binding,
                            selected,
                            bound_variables,
                        )
                    })?);
                    index += 2;
                }
                term_source_0 @ Term::ProgramValue(_)
                    if let Some(ProgramValue::Pointer(pointer)) =
                        term_source_0.program_value_native() =>
                {
                    call_arguments.push(synthesize_surface_pointer_expression(
                        pointer,
                        parameter_binding,
                        state,
                        bound_variables,
                    )?);
                    index += 1;
                }
                term_source_0 @ Term::ProgramValue(_)
                    if let Some(
                        ProgramValue::Int8(value)
                        | ProgramValue::UInt8(value)
                        | ProgramValue::Int16(value)
                        | ProgramValue::UInt16(value)
                        | ProgramValue::Int32(value)
                        | ProgramValue::UInt32(value)
                        | ProgramValue::Int64(value)
                        | ProgramValue::UInt64(value)
                        | ProgramValue::Int128(value)
                        | ProgramValue::UInt128(value),
                    ) = term_source_0.program_value_native() =>
                {
                    call_arguments.push(synthesize_surface_bitvector(
                        value,
                        parameter_binding,
                        state,
                        bound_variables,
                    )?);
                    index += 1;
                }
                _ => return None,
            }
        }
        return Some(SyntaxProposition::PredicateCall {
            name: crate::kernel::predicate_source_name(name)?.to_string(),
            arguments: call_arguments,
        });
    }
    if let Proposition::ResourceViewable {
        memory, resource, ..
    } = proposition
    {
        let viewable = SyntaxProposition::ResourceViewable {
            resource: synthesize_surface_resource_subject(
                resource,
                parameter_binding,
                state,
                bound_variables,
            )?,
        };
        if state.memory() == memory {
            return Some(viewable);
        }
        let selector = if SYNTHESIS_ENTRY_STATE.with(|slot| {
            slot.borrow()
                .as_ref()
                .is_some_and(|entry| entry.memory() == memory)
        }) {
            ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Function,
                kind: ProgramPointKind::Entry,
            })
        } else {
            SYNTHESIS_REFERENCE_STATE.with(|slot| {
                let slot = slot.borrow();
                let (retained_state, selector) = slot.as_ref()?;
                (retained_state.memory() == memory).then(|| selector.clone())
            })?
        };
        return Some(SyntaxProposition::At {
            selector,
            proposition: Box::new(viewable),
        });
    }
    if let Proposition::ResourceContains { parent, child } = proposition {
        return Some(SyntaxProposition::Contains {
            parent: synthesize_surface_resource_subject(
                parent,
                parameter_binding,
                state,
                bound_variables,
            )?,
            child: synthesize_surface_resource_subject(
                child,
                parameter_binding,
                state,
                bound_variables,
            )?,
        });
    }
    if let Proposition::ResourceSeparate { left, right } = proposition {
        return Some(SyntaxProposition::Separate {
            left: synthesize_surface_resource_subject(
                left,
                parameter_binding,
                state,
                bound_variables,
            )?,
            right: synthesize_surface_resource_subject(
                right,
                parameter_binding,
                state,
                bound_variables,
            )?,
        });
    }
    if let Proposition::MemoryReadDefined {
        at,
        memory,
        pointer,
        value_type,
        ..
    } = proposition
    {
        let matches_point = |candidate: &ExecutionState| match at {
            Some(id) => candidate.observation_point_id() == Some(*id),
            None => candidate.memory() == memory,
        };
        let historical = if matches_point(state) {
            None
        } else {
            Some(
                SYNTHESIS_ENTRY_STATE
                    .with(|slot| {
                        let slot = slot.borrow();
                        let entry = slot.as_ref().filter(|entry| matches_point(entry))?;
                        Some((
                            ProgramPointSelector::ProgramPoint(ProgramPointRef {
                                region: CodeRegionRef::Function,
                                kind: ProgramPointKind::Entry,
                            }),
                            entry.clone(),
                        ))
                    })
                    .or_else(|| {
                        SYNTHESIS_REFERENCE_STATE.with(|slot| {
                            let slot = slot.borrow();
                            let (retained, selector) = slot.as_ref()?;
                            matches_point(retained).then(|| (selector.clone(), retained.clone()))
                        })
                    })
                    .or_else(|| {
                        SYNTHESIS_RECORDED_POINTS.with(|slot| {
                            let slot = slot.borrow();
                            let points = slot.as_ref()?;
                            let selector = points.point_name((*at)?)?;
                            let recorded = points.get_exact(selector)?;
                            matches_point(recorded).then(|| (selector.clone(), recorded.clone()))
                        })
                    })?,
            )
        };
        let read_state = historical.as_ref().map_or(state, |(_, state)| state);
        let pointer = synthesize_surface_pointer_expression(
            pointer,
            parameter_binding,
            read_state,
            bound_variables,
        )?;
        let validity = SyntaxProposition::Defined {
            expression: synthesize_typed_load(pointer, *value_type),
        };
        return Some(match historical {
            Some((selector, _)) => SyntaxProposition::At {
                selector,
                proposition: Box::new(validity),
            },
            None => validity,
        });
    }
    if let Proposition::MemoryLoadable {
        memory,
        base,
        bytes,
        wide: false,
        ..
    } = proposition
    {
        let loadable = synthesize_zero_based_loadable_segment(
            base,
            bytes.old_form(),
            parameter_binding,
            state,
            bound_variables,
        )
        .or_else(|| {
            synthesize_named_range_loadable_segment(
                base,
                bytes.old_form(),
                parameter_binding,
                state,
                bound_variables,
            )
        })?;
        if state.memory() == memory {
            return Some(loadable);
        }
        let at_entry = SYNTHESIS_ENTRY_STATE.with(|slot| {
            slot.borrow()
                .as_ref()
                .is_some_and(|entry| entry.memory() == memory)
        });
        if at_entry {
            return Some(SyntaxProposition::At {
                selector: ProgramPointSelector::ProgramPoint(ProgramPointRef {
                    region: CodeRegionRef::Function,
                    kind: ProgramPointKind::Entry,
                }),
                proposition: Box::new(loadable),
            });
        }
        let program_point_selector = SYNTHESIS_REFERENCE_STATE.with(|slot| {
            let slot = slot.borrow();
            let (retained_state, selector) = slot.as_ref()?;
            (retained_state.memory() == memory).then(|| selector.clone())
        });
        return Some(if let Some(selector) = program_point_selector {
            SyntaxProposition::At {
                selector,
                proposition: Box::new(loadable),
            }
        } else {
            loadable
        });
    }
    if let Proposition::Not(body) = proposition {
        return Some(SyntaxProposition::Not(Box::new(
            synthesize_surface_proposition_with_bound_variables(
                body,
                parameter_binding,
                state,
                bound_variables,
            )?,
        )));
    }
    let Proposition::ConditionIs(condition, value) = proposition else {
        return None;
    };
    let raise_float = |operand: crate::kernel::FloatOperandView<'_>| {
        let imported;
        let root = match operand {
            crate::kernel::FloatOperandView::Shared(root) => root,
            crate::kernel::FloatOperandView::Native(format, term) => {
                imported = crate::kernel::KernelTermImport::default().float(format, term);
                &imported
            }
        };
        let raised = raise_kernel_term(root, parameter_binding, state, bound_variables)?;
        // A comparison otherwise reads a written sum as Integer arithmetic.
        if operand.binary().is_some() || operand.negate().is_some() {
            synthesize_observation_operand(raised, operand.format().program_type())
        } else {
            Some(raised)
        }
    };
    let float_predicate =
        if let Some((_, operator, [left, right])) = condition.operand_view().float_comparison() {
            Some(SyntaxProposition::Comparison {
                left: raise_float(left)?,
                operator: surface_float_comparison_operator(operator),
                right: raise_float(right)?,
            })
        } else if let Some((_, classification, operand)) =
            condition.operand_view().float_classification()
        {
            Some(SyntaxProposition::FloatClassification {
                expression: raise_float(operand)?,
                classification: surface_float_classification(classification),
            })
        } else {
            None
        };
    if let Some(predicate) = float_predicate {
        // Opposite order operators are not equivalent under IEEE NaN semantics.
        return Some(if *value {
            predicate
        } else {
            SyntaxProposition::Not(Box::new(predicate))
        });
    }
    if let OldConditionTerm::AlgebraicEqual(left, right) = condition.old_form() {
        return Some(SyntaxProposition::Comparison {
            left: synthesize_surface_algebraic(left, parameter_binding, state, bound_variables)?,
            operator: if *value {
                ComparisonOperator::Equal
            } else {
                ComparisonOperator::NotEqual
            },
            right: synthesize_surface_algebraic(right, parameter_binding, state, bound_variables)?,
        });
    }
    // A closed `bool` comparison is spelled as written: `true == false`
    // lowers back to exactly this retained comparison.
    if let OldConditionTerm::BoolEqual(left, right) = condition.old_form()
        && let (OldConditionTerm::Constant(left), OldConditionTerm::Constant(right)) =
            (left.as_ref(), right.as_ref())
    {
        return Some(SyntaxProposition::Comparison {
            left: crate::surface::bool_literal(*left),
            operator: if *value {
                ComparisonOperator::Equal
            } else {
                ComparisonOperator::NotEqual
            },
            right: crate::surface::bool_literal(*right),
        });
    }
    if matches!(
        condition.old_form(),
        OldConditionTerm::Variable(_)
            | OldConditionTerm::BoolApplication(_)
            | OldConditionTerm::BoolIf { .. }
            | OldConditionTerm::BoolEqual(..)
    ) {
        let claim = bool_truth(synthesize_surface_bool(
            condition.old_form(),
            parameter_binding,
            state,
            bound_variables,
        )?);
        return Some(if *value {
            claim
        } else {
            SyntaxProposition::Not(Box::new(claim))
        });
    }
    if let OldConditionTerm::Overflows {
        format: MachineIntegerType::Int32 | MachineIntegerType::Int64,
        op:
            op @ (OverflowOperation::Add | OverflowOperation::Subtract | OverflowOperation::Multiply),
        left,
        right,
    } = condition.old_form()
    {
        // Definedness names this operation, not a local that already holds
        // its result. `defined(result)` would lose the operation's domain.
        let left = Box::new(synthesize_surface_bitvector(
            left,
            parameter_binding,
            state,
            bound_variables,
        )?);
        let right = Box::new(synthesize_surface_bitvector(
            right,
            parameter_binding,
            state,
            bound_variables,
        )?);
        let expression = match op {
            OverflowOperation::Add => SyntaxTerm::Add(left, right),
            OverflowOperation::Subtract => SyntaxTerm::Subtract(left, right),
            OverflowOperation::Multiply => SyntaxTerm::Multiply(left, right),
            _ => unreachable!("arithmetic overflow matched above"),
        };
        let defined = SyntaxProposition::Defined { expression };
        return Some(if *value {
            SyntaxProposition::Not(Box::new(defined))
        } else {
            defined
        });
    }
    if let Some(condition) = condition.operand_view().constant() {
        // The `bool` literal lowers to exactly this constant condition. A
        // closed comparison such as `0 == 1` does not: lowering retains it.
        let literal = SyntaxProposition::Value(crate::surface::bool_literal(condition));
        return Some(if *value {
            literal
        } else {
            SyntaxProposition::Not(Box::new(literal))
        });
    }
    if let OldConditionTerm::AddressOffsetEqual(left, right) = condition.old_form() {
        return Some(SyntaxProposition::Comparison {
            left: synthesize_surface_pointer_offset(
                left,
                parameter_binding,
                state,
                bound_variables,
            )?,
            operator: if *value {
                ComparisonOperator::Equal
            } else {
                ComparisonOperator::NotEqual
            },
            right: synthesize_surface_pointer_offset(
                right,
                parameter_binding,
                state,
                bound_variables,
            )?,
        });
    }
    if let OldConditionTerm::PointerEqual(left, right) = condition.old_form() {
        return Some(SyntaxProposition::Comparison {
            left: synthesize_pointer_equality_operand(
                left,
                parameter_binding,
                state,
                bound_variables,
            )?,
            operator: if *value {
                ComparisonOperator::Equal
            } else {
                ComparisonOperator::NotEqual
            },
            right: synthesize_pointer_equality_operand(
                right,
                parameter_binding,
                state,
                bound_variables,
            )?,
        });
    }
    // A pointer equality raises as contract `p == q`, which lowers to it; the
    // weaker `address(p) == address(q)` is the address-word equality a C
    // comparison states (`design/pointer-subobject-bounds.md`, Phase B).
    if let OldConditionTerm::AddressEqual(left, right) = condition.old_form() {
        let pointer = synthesize_surface_pointer_expression;
        return Some(SyntaxProposition::Comparison {
            left: pointer(left, parameter_binding, state, bound_variables)?,
            operator: if *value {
                ComparisonOperator::Equal
            } else {
                ComparisonOperator::NotEqual
            },
            right: pointer(right, parameter_binding, state, bound_variables)?,
        });
    }
    if let Some([left, right]) =
        crate::kernel::machine_integer::comparison::native_int32_fold_equality(condition.old_form())
    {
        let observe = |term: &OldMachineTerm| -> Option<crate::kernel::SharedIntegerTerm> {
            crate::kernel::IntegerTerm::from_machine(MachineIntegerType::Int32, term.clone())
                .map(Into::into)
        };
        return integer_observation_comparison(
            &observe(left)?,
            if *value {
                ComparisonOperator::Equal
            } else {
                ComparisonOperator::NotEqual
            },
            &observe(right)?,
            true,
            parameter_binding,
            state,
            bound_variables,
        );
    }
    if let OldConditionTerm::Compare {
        format,
        relation,
        left,
        right,
    } = condition.old_form()
        && matches!(format.format().bits(), 32 | 64)
        && let Some(operator) = match relation {
            CompareRelation::LessThan => Some(ComparisonOperator::LessThan),
            CompareRelation::LessEqual => Some(ComparisonOperator::LessEqual),
            CompareRelation::Equal => Some(ComparisonOperator::Equal),
            _ => None,
        }
    {
        let converted = |term: &OldMachineTerm, observed| matches!(term, OldMachineTerm::IntegerToMachine { destination, .. } if *destination == observed);
        let conditional = |term: &OldMachineTerm, observed| {
            matches!(term, OldMachineTerm::If { then_term, else_term, .. }
                if converted(then_term, observed) || converted(else_term, observed))
        };
        let operands = [left.as_ref(), right.as_ref()];
        // An unsigned 64-bit equality is filed at Int64. Its observation
        // still needs the unsigned type carried by the conversion.
        let observed = if *format == MachineIntegerType::Int64
            && *relation == CompareRelation::Equal
            && operands
                .iter()
                .any(|term| conditional(term, MachineIntegerType::UInt64))
        {
            MachineIntegerType::UInt64
        } else {
            *format
        };
        if operands.iter().any(|term| conditional(term, observed))
            && operands.iter().copied().all(|operand| {
                conditional(operand, observed)
                    || converted(operand, observed)
                    || matches!(operand, OldMachineTerm::Variable(_))
                    || observed.constant_from_term(operand).is_some()
            })
        {
            // The Integer observation spelling produces this native comparison.
            // A direct word comparison over these conditional arms keeps an
            // Integer comparison instead.
            let observe = |word: &OldMachineTerm| {
                crate::kernel::IntegerTerm::from_machine(observed, word.clone()).map(Into::into)
            };
            return integer_observation_comparison(
                &observe(left)?,
                operator,
                &observe(right)?,
                *value,
                parameter_binding,
                state,
                bound_variables,
            );
        }
    }
    if let Some(comparison) = synthesize_unsigned_comparison(
        condition.old_form(),
        parameter_binding,
        state,
        bound_variables,
    ) {
        return Some(if *value {
            comparison
        } else {
            SyntaxProposition::Not(Box::new(comparison))
        });
    }
    // Keep the narrow interpretation even when rewriting removed the last
    // symbolic operand. Observing a literal as Integer would discard its type.
    if let OldConditionTerm::Compare {
        format:
            format @ (MachineIntegerType::Int8
            | MachineIntegerType::UInt8
            | MachineIntegerType::Int16
            | MachineIntegerType::UInt16),
        relation,
        left,
        right,
    } = condition.old_form()
    {
        // Symbolic observations retain their established Integer spelling.
        // A literal beside one such observation is recovered at that format.
        if format.constant_from_term(left).is_none() || format.constant_from_term(right).is_none() {
            let observe = |term: &OldMachineTerm| -> Option<crate::kernel::SharedIntegerTerm> {
                crate::kernel::IntegerTerm::from_machine(*format, term.clone()).map(Into::into)
            };
            let (l, r) = (observe(left)?, observe(right)?);
            let integer = match relation {
                CompareRelation::LessThan => OldConditionTerm::IntegerLessThan(l, r),
                CompareRelation::LessEqual => OldConditionTerm::IntegerLessEqual(l, r),
                CompareRelation::GreaterThan => OldConditionTerm::IntegerGreaterThan(l, r),
                CompareRelation::GreaterEqual => OldConditionTerm::IntegerGreaterEqual(l, r),
                CompareRelation::Equal => OldConditionTerm::IntegerEqual(l, r),
            };
            return synthesize_surface_atomic_proposition(
                &Proposition::condition_is(integer, *value),
                parameter_binding,
                state,
                bound_variables,
            );
        }
        let operand = |term: &OldMachineTerm| {
            // Narrow suffixes such as `9u8` require a Rust sidecar. Every
            // narrow value fits an ordinary int32 literal under this cast.
            let value: i32 = format
                .constant_from_term(term)
                .expect("both narrow operands are literal")
                .to_integer()
                .try_into()
                .expect("a narrow value fits int32");
            synthesize_observation_operand(
                SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(value as u32))),
                format.program_type(),
            )
        };
        let comparison = SyntaxProposition::Comparison {
            left: operand(left)?,
            operator: match relation {
                CompareRelation::LessThan => ComparisonOperator::LessThan,
                CompareRelation::LessEqual => ComparisonOperator::LessEqual,
                CompareRelation::GreaterThan => ComparisonOperator::GreaterThan,
                CompareRelation::GreaterEqual => ComparisonOperator::GreaterEqual,
                CompareRelation::Equal => ComparisonOperator::Equal,
            },
            right: operand(right)?,
        };
        return Some(if *value {
            comparison
        } else {
            SyntaxProposition::Not(Box::new(comparison))
        });
    }
    let (left, operator, right) = match condition.old_form() {
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left,
            right,
        }
        | OldConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::LessThan,
            left,
            right,
        }
        | OldConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::LessThan,
            left,
            right,
        } => (left, ComparisonOperator::LessThan, right),
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left,
            right,
        }
        | OldConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::LessEqual,
            left,
            right,
        }
        | OldConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::LessEqual,
            left,
            right,
        } => (left, ComparisonOperator::LessEqual, right),
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterThan,
            left,
            right,
        }
        | OldConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::GreaterThan,
            left,
            right,
        }
        | OldConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::GreaterThan,
            left,
            right,
        } => (left, ComparisonOperator::GreaterThan, right),
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterEqual,
            left,
            right,
        }
        | OldConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::GreaterEqual,
            left,
            right,
        }
        | OldConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::GreaterEqual,
            left,
            right,
        } => (left, ComparisonOperator::GreaterEqual, right),
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        }
        | OldConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left,
            right,
        } => (left, ComparisonOperator::Equal, right),
        _ => return None,
    };
    // An `int32` order reads its operands' words as `int32`. An operand
    // spelled in `uint32` (a `uint32` local or parameter whose word a sign
    // cast compared signed) would make the spelled comparison unsigned, a
    // different fact, so it is written converted, as `u as int32 < 0`.
    let signed_order = matches!(
        condition.old_form(),
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan
                | CompareRelation::LessEqual
                | CompareRelation::GreaterThan
                | CompareRelation::GreaterEqual,
            ..
        }
    );
    let signed_word = matches!(
        condition.old_form(),
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            ..
        }
    );
    let unsigned_word_equality = matches!(
        condition.old_form(),
        OldConditionTerm::Compare {
            format: MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            ..
        }
    );
    // A 64-bit equality the source wrote between a 64-bit word and a 32-bit
    // one holds the narrow operand widened. Writing that widening as a cast
    // gives two operands of one format, which lower to a different
    // comparison; the narrow operand is written as the source had it and
    // lowering widens it again. Against a constant the cast stays: lowering
    // decides or narrows a widened word compared with a literal, so only the
    // one-format comparison keeps it.
    fn widened(term: &OldMachineTerm) -> Option<(&OldMachineTerm, bool)> {
        match term {
            cast_term!(Int64From32, value) | cast_term!(UInt64FromInt32, value) => {
                Some((value.as_ref(), false))
            }
            cast_term!(Int64FromUInt32, value) | cast_term!(UInt64From32, value) => {
                Some((value.as_ref(), true))
            }
            _ => None,
        }
    }
    let wide_constant =
        |term: &OldMachineTerm| term.int64_as_const().is_some() || term.uint64_as_const().is_some();
    let narrow_operand = matches!(
        condition.old_form(),
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            ..
        }
    )
    .then(|| match (widened(left), widened(right)) {
        (Some(narrow), None) if !wide_constant(right) => Some((left, narrow)),
        (None, Some(narrow)) if !wide_constant(left) => Some((right, narrow)),
        _ => None,
    })
    .flatten();
    let operand = |term: &OldMachineTerm| {
        if let Some((widening, (narrow, unsigned))) = narrow_operand
            && std::ptr::eq::<OldMachineTerm>(&**widening, term)
        {
            let narrow =
                synthesize_surface_bitvector(narrow, parameter_binding, state, bound_variables)?;
            return if unsigned {
                synthesize_uint32_operand(narrow)
            } else {
                synthesize_int32_operand(narrow)
            };
        }
        // A `uint32` equality's constant whose word reads negative as an
        // `int32` is written as its `uint32` value: the word it compares is
        // the same either way, but `-56` beside a `uint32` value would read
        // as a claim it cannot satisfy. Smaller constants read alike.
        if unsigned_word_equality
            && let Some(bits) = term.constant32()
            && bits >= 1 << 31
        {
            return Some(SyntaxTerm::ProgramExpression(
                crate::kernel::program_expression::uint32_literal(bits),
            ));
        }
        // Wide comparisons retain signedness at each read and operation.
        // Reconstruct their shared operands rather than defaulting a Bits64
        // read to int64 before an unsigned operation consumes it.
        let expression = if let OldConditionTerm::Compare {
            format: format @ (MachineIntegerType::Int64 | MachineIntegerType::UInt64),
            relation,
            ..
        } = condition.old_form()
        {
            let root = crate::kernel::KernelTermImport::default().machine(*format, term);
            match root.node() {
                // A 64-bit equality reads both words at its own format,
                // so a call there is the call as declared: lowering
                // `x == f(..)` reads `f`'s word at the equality's format
                // itself. A narrower call would be a widening cast here,
                // not a bare call, so no width changes. Casting the call
                // to the format would lower to a cast node instead.
                crate::kernel::KernelTermNode::Call { name, arguments }
                    if *relation == CompareRelation::Equal =>
                {
                    raise_call(name, arguments, parameter_binding, state, bound_variables)?
                }
                // A read there is likewise the read as written, `s.value`,
                // and not a typed word read at the equality's signedness
                // (`load<int64>(&s)`), which lowers to a different read.
                crate::kernel::KernelTermNode::MemoryLoad { .. }
                    if *relation == CompareRelation::Equal
                        && let Some(read) = synthesize_surface_bitvector(
                            term,
                            parameter_binding,
                            state,
                            bound_variables,
                        ) =>
                {
                    read
                }
                _ => raise_kernel_term(&root, parameter_binding, state, bound_variables)?,
            }
        } else {
            synthesize_surface_bitvector(term, parameter_binding, state, bound_variables)?
        };
        let mut expression = expression;
        if signed_word {
            spell_signed_low_word_operand(term, &mut expression);
        }
        // A bare arithmetic expression in a reparsed equality can become Integer arithmetic.
        // Give the generated uint32 word expression an explicit machine context.
        if unsigned_word_equality
            && matches!(
                term,
                OldMachineTerm::Binary {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    op: MachineBinaryOp::Add
                        | MachineBinaryOp::Subtract
                        | MachineBinaryOp::Multiply,
                    ..
                }
            )
            && matches!(
                expression,
                SyntaxTerm::Add(..) | SyntaxTerm::Subtract(..) | SyntaxTerm::Multiply(..)
            )
        {
            synthesize_uint32_operand(expression)
        } else if (signed_word && is_signed_variable_arithmetic32(term, &expression))
            || (signed_order
                && (bitvector_spells_uint32(term, parameter_binding, state, bound_variables)
                    || matches!(
                        expression,
                        SyntaxTerm::Add(..) | SyntaxTerm::Subtract(..) | SyntaxTerm::Multiply(..)
                    )))
        {
            synthesize_int32_operand(expression)
        } else {
            Some(expression)
        }
    };
    // Both operands are synthesized before either refusal is read, as
    // they were before the conversion: synthesis charges work.
    let surface_left = operand(left);
    let surface_right = operand(right);
    let comparison = SyntaxProposition::Comparison {
        left: surface_left?,
        operator,
        right: surface_right?,
    };
    if *value {
        Some(comparison)
    } else if operator == ComparisonOperator::Equal {
        let SyntaxProposition::Comparison { left, right, .. } = comparison else {
            unreachable!()
        };
        Some(SyntaxProposition::Comparison {
            left,
            operator: ComparisonOperator::NotEqual,
            right,
        })
    } else {
        Some(SyntaxProposition::Not(Box::new(comparison)))
    }
}

fn is_signed_variable_arithmetic32(term: &OldMachineTerm, expression: &SyntaxTerm) -> bool {
    matches!(
        term,
        OldMachineTerm::Binary {
            format: MachineIntegerType::Int32,
            op: MachineBinaryOp::Add | MachineBinaryOp::Subtract | MachineBinaryOp::Multiply,
            left,
            right,
        } if matches!((left.as_ref(), right.as_ref()), (OldMachineTerm::Variable(_), OldMachineTerm::Variable(_)))
    ) && matches!(
        expression,
        SyntaxTerm::Add(..) | SyntaxTerm::Subtract(..) | SyntaxTerm::Multiply(..)
    )
}

/// The low-word node carries no destination signedness. Retarget its cast
/// in a signed comparison or its immediate conditional arms.
fn spell_signed_low_word_operand(term: &OldMachineTerm, expression: &mut SyntaxTerm) {
    let low_word = |term: &OldMachineTerm, expression: &mut SyntaxTerm| {
        if matches!(term, cast_term!(UInt32From64, _))
            && let SyntaxTerm::CUnary {
                lowered: ProgramExpression::Cast { target_type, .. },
                ..
            } = expression
            && *target_type == ProgramType::UInt32
        {
            *target_type = ProgramType::Int32;
        }
    };
    if let (
        OldMachineTerm::If {
            then_term,
            else_term,
            ..
        },
        SyntaxTerm::If {
            then_branch,
            else_branch,
            ..
        },
    ) = (term, &mut *expression)
    {
        low_word(then_term, then_branch);
        low_word(else_term, else_branch);
    } else {
        low_word(term, expression);
    }
}

/// Preserve the Integer context without introducing a lexical binding.
pub(super) fn integer_typed_expression(value: SyntaxTerm) -> SyntaxTerm {
    SyntaxTerm::IntegerContext(Box::new(value))
}

/// Spell compound word comparisons as Integer observations in an arm label.
/// Written arithmetic can otherwise be elaborated as mathematical arithmetic
/// before the comparison sees its native operand type.
pub(super) fn spell_conjunct_observations(goal: &Proposition, surface: &mut SyntaxProposition) {
    match (goal, surface) {
        (Proposition::And(a, b), SyntaxProposition::And(left, right))
        | (Proposition::Or(a, b), SyntaxProposition::Or(left, right))
        | (Proposition::Implies(a, b), SyntaxProposition::Implies(left, right)) => {
            spell_conjunct_observations(a, left);
            spell_conjunct_observations(b, right);
        }
        (Proposition::Not(body), SyntaxProposition::Not(surface_body))
        | (
            Proposition::ForAll { body, .. },
            SyntaxProposition::ForAll {
                body: surface_body, ..
            },
        )
        | (
            Proposition::Exists { body, .. },
            SyntaxProposition::Exists {
                body: surface_body, ..
            },
        ) => {
            spell_conjunct_observations(body, surface_body);
        }
        (goal @ Proposition::ConditionIs(..), SyntaxProposition::Not(surface_body)) => {
            spell_conjunct_observations(goal, surface_body);
        }
        (goal, SyntaxProposition::Comparison { left, right, .. }) => {
            use crate::kernel::BooleanOperandView as B;
            if let Proposition::ConditionIs(condition, _) = goal
                && let Some((format, _, operands)) = match condition.operand_view() {
                    B::Shared(root) => root.cached_condition_output().map_or_else(
                        || B::Shared(root).comparison(),
                        |native| B::Native(native).comparison(),
                    ),
                    view => view.comparison(),
                }
                && matches!(
                    format,
                    MachineIntegerType::Int32 | MachineIntegerType::Int64
                )
                && operands.iter().any(|operand| {
                    matches!(
                        operand.binary(),
                        Some((
                            _,
                            MachineBinaryOp::Add
                                | MachineBinaryOp::Subtract
                                | MachineBinaryOp::Multiply,
                            _
                        ))
                    )
                })
            {
                for expression in [left, right] {
                    *expression = SyntaxTerm::Call {
                        name: "to_integer".into(),
                        arguments: vec![expression.clone()],
                    };
                }
            }
        }
        _ => {}
    }
}

/// An Integer arithmetic term over machine observations, spelled with
/// `to_integer` around each observation and named truncating operations.
/// Opaque specification applications retain their source boundary.
/// Whether a comparison written over these machine operands lowers to the
/// Integer comparison of their observations rather than the native
/// comparison: logical lowering keeps a comparison over a retained compound
/// operand Integer (`comparison::condition_for_operand_views`). This is the
/// lowering's own operand-root test, so the raiser picks the spelling that
/// lowers back to the term it raises.
fn machine_spelling_lowers_to_integer(
    format: MachineIntegerType,
    relation: CompareRelation,
    operands: [crate::kernel::KernelTerm; 2],
) -> bool {
    use crate::kernel::machine_integer::comparison;
    let operands = operands
        .each_ref()
        .map(crate::kernel::MachineOperandView::Shared);
    !comparison::retains_int32_match(format, operands)
        && !matches!(
            comparison::logical_condition_for_operand_views(format, relation, operands),
            OldConditionTerm::Compare { .. } | OldConditionTerm::Constant(_)
        )
}

fn raise_integer_comparison(
    operator: crate::kernel::IntegerComparisonOperator,
    operands: &[crate::kernel::SharedIntegerTerm; 2],
    value: bool,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxProposition> {
    // An Integer comparison of observations keeps machine Surface operands
    // exactly when the machine spelling lowers back to it: lowering keeps a
    // comparison over a retained compound operand (an operation, a
    // conditional, a cast) Integer. Over atomic operands the machine
    // spelling lowers native, so those keep explicit `to_integer`.
    if let Some(view) =
        crate::kernel::machine_integer::comparison::structural_integer_comparison_view(
            operator,
            operands.each_ref(),
        )
        && matches!(
            view.format,
            MachineIntegerType::Int32
                | MachineIntegerType::UInt32
                | MachineIntegerType::Int64
                | MachineIntegerType::UInt64
        )
        && machine_spelling_lowers_to_integer(
            view.format,
            view.relation,
            view.operands.each_ref().map(|operand| {
                crate::kernel::KernelTerm::retained_machine_operand(
                    view.format,
                    operand.operand_view(),
                )
            }),
        )
    {
        let operator = match view.relation {
            CompareRelation::Equal => ComparisonOperator::Equal,
            CompareRelation::LessThan => ComparisonOperator::LessThan,
            CompareRelation::LessEqual => ComparisonOperator::LessEqual,
            CompareRelation::GreaterThan => ComparisonOperator::GreaterThan,
            CompareRelation::GreaterEqual => ComparisonOperator::GreaterEqual,
        };
        let raise = |operand: &crate::kernel::machine_integer::comparison::ComparisonOperand<
            '_,
        >| {
            let root = crate::kernel::KernelTerm::retained_machine_operand(
                view.format,
                operand.operand_view(),
            );
            raise_kernel_term(&root, parameter_binding, state, bound_variables).and_then(
                |expression| synthesize_observation_operand(expression, view.format.program_type()),
            )
        };
        let comparison = SyntaxProposition::Comparison {
            left: raise(&view.operands[0])?,
            operator,
            right: raise(&view.operands[1])?,
        };
        return Some(if value != view.negated {
            comparison
        } else {
            SyntaxProposition::Not(Box::new(comparison))
        });
    }
    use crate::kernel::IntegerComparisonOperator as Op;
    let operator = match operator {
        Op::Equal => ComparisonOperator::Equal,
        Op::NotEqual => ComparisonOperator::NotEqual,
        Op::LessThan => ComparisonOperator::LessThan,
        Op::LessEqual => ComparisonOperator::LessEqual,
        Op::GreaterThan => ComparisonOperator::GreaterThan,
        Op::GreaterEqual => ComparisonOperator::GreaterEqual,
    };
    integer_observation_comparison(
        &operands[0],
        operator,
        &operands[1],
        value,
        parameter_binding,
        state,
        bound_variables,
    )
}

/// An Integer comparison of two Integer terms, printed by
/// `print_comparison`: an Integer marking appears only when neither raised
/// operand spells an Integer, such as `3 == n` after a rewrite removed the
/// last observation.
#[allow(clippy::too_many_arguments)]
fn integer_observation_comparison(
    left: &crate::kernel::SharedIntegerTerm,
    operator: ComparisonOperator,
    right: &crate::kernel::SharedIntegerTerm,
    value: bool,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxProposition> {
    let integer_calls = integer_call_names([left, right]);
    let comparison = crate::surface::print_comparison(
        crate::surface::ComparisonKind::Integer,
        synthesize_surface_integer(left, parameter_binding, state, bound_variables)?,
        operator,
        synthesize_surface_integer(right, parameter_binding, state, bound_variables)?,
        &|name| integer_calls.contains(name),
    );
    Some(if value {
        comparison
    } else {
        SyntaxProposition::Not(Box::new(comparison))
    })
}

/// The names of the Integer-valued calls on the arithmetic spine of these
/// Integer terms: the calls their raised Syntax can show where
/// `spells_integer` looks. A call is Integer by its declaration, which the
/// kernel call node's type records. One visit per spine node.
fn integer_call_names<'t>(
    terms: impl IntoIterator<Item = &'t crate::kernel::SharedIntegerTerm>,
) -> BTreeSet<String> {
    use crate::kernel::KernelTermNode as N;
    let mut import = crate::kernel::KernelTermImport::default();
    let mut pending = terms
        .into_iter()
        .map(|term| import.integer(term))
        .collect::<Vec<_>>();
    let mut names = BTreeSet::new();
    while let Some(root) = pending.pop() {
        match root.node() {
            N::Call { name, .. } if matches!(root.ty(), crate::kernel::KernelType::Integer) => {
                names.insert(name.to_string());
            }
            N::IntegerOperation { arguments, .. } => pending.extend(arguments.iter().cloned()),
            _ => {}
        }
    }
    names
}

fn synthesize_surface_integer(
    term: &crate::kernel::SharedIntegerTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    // Keep the carrier's bridge identity: a native clone and re-intern here
    // discards the caller's shared handoff before reaching the common renderer.
    let term = crate::kernel::KernelTermImport::default().integer(term);
    raise_kernel_term(&term, parameter_binding, state, bound_variables)
}

// The comparison renderer spells a proposition used as a Bool via
// `if guard { true } else { false }`. An Integer or algebraic `if` expects a
// proposition directly, so recover the comparison instead of wrapping it.
fn raise_value_if_guard(
    guard: &crate::kernel::KernelTerm,
    expression: SyntaxTerm,
) -> SyntaxProposition {
    use crate::kernel::KernelTermNode as Node;
    match (guard.node(), expression) {
        (Node::BoolLiteral(_), literal) => SyntaxProposition::Value(literal),
        (
            Node::BoolCompare { .. } | Node::IntegerCompare { .. },
            SyntaxTerm::If {
                condition,
                then_branch,
                else_branch,
            },
        ) if bool_literal_value(&then_branch) == Some(true)
            && bool_literal_value(&else_branch) == Some(false) =>
        {
            *condition
        }
        (_, expression) => bool_truth(expression),
    }
}

// Keep this construction outside the recursive general dispatch frame.
fn raise_algebraic_if<'a>(
    arguments: &'a [crate::kernel::KernelTerm; 3],
    mut raise: impl FnMut(&'a crate::kernel::KernelTerm) -> Option<SyntaxTerm>,
) -> Option<SyntaxTerm> {
    Some(SyntaxTerm::If {
        condition: Box::new(raise_value_if_guard(&arguments[0], raise(&arguments[0])?)),
        then_branch: Box::new(raise(&arguments[1])?),
        else_branch: Box::new(raise(&arguments[2])?),
    })
}

// Complete pointer call arguments use their exact proof-local source name,
// just as native arguments do. General pointer-expression synthesis can pick
// an address spelling with different producer metadata; it is not this
// argument boundary's policy.
fn raise_call_argument(
    term: &crate::kernel::KernelTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    use crate::kernel::KernelTermNode as Node;
    match term.node() {
        Node::ObservedPointer(value) => {
            raise_call_argument(value.source(), parameter_binding, state, bound_variables)
        }
        // A pointer a proof name holds is spelled by that name; any other
        // pointer argument is spelled as the pointer itself.
        Node::Pointer(value)
        | Node::PointerRead { value, .. }
        | Node::PointerArithmetic { value, .. }
        | Node::PointerCall { value, .. }
            if let Some(name) = pointer_names::shared_name(value) =>
        {
            Some(SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                name.into(),
            )))
        }
        // A null pointer argument is the literal `0` the parameter's type
        // reads, as source writes it; an `int32` zero would not fit it.
        Node::Pointer(_) | Node::PointerRead { .. } | Node::PointerArithmetic { .. }
            if matches!(
                term.old_pointer_value(),
                Some(ProgramValue::Pointer(pointer)) if pointer.address() == &Address::null()
            ) =>
        {
            Some(SyntaxTerm::IntegerLiteral("0".into()))
        }
        _ => raise_kernel_term(term, parameter_binding, state, bound_variables),
    }
}

fn raise_call(
    name: &str,
    arguments: &[crate::kernel::KernelTerm],
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    Some(SyntaxTerm::Call {
        name: generic_instance_source_name(name).into(),
        arguments: arguments
            .iter()
            .map(|argument| {
                raise_call_argument(argument, parameter_binding, state, bound_variables)
            })
            .collect::<Option<Vec<_>>>()?,
    })
}

fn surface_float_classification(
    classification: crate::kernel::FloatClassification,
) -> syntax::CFloatClassification {
    use crate::kernel::FloatClassification as C;
    match classification {
        C::Finite => syntax::CFloatClassification::Finite,
        C::Infinite => syntax::CFloatClassification::Infinite,
        C::Zero => syntax::CFloatClassification::Zero,
        C::Subnormal => syntax::CFloatClassification::Subnormal,
        C::Nan => syntax::CFloatClassification::Nan,
    }
}

fn surface_float_comparison_operator(
    operator: crate::kernel::ComparisonOperator,
) -> ComparisonOperator {
    use crate::kernel::ComparisonOperator as C;
    match operator {
        C::Equal => ComparisonOperator::Equal,
        C::NotEqual => ComparisonOperator::NotEqual,
        C::LessThan => ComparisonOperator::LessThan,
        C::LessEqual => ComparisonOperator::LessEqual,
        C::GreaterThan => ComparisonOperator::GreaterThan,
        C::GreaterEqual => ComparisonOperator::GreaterEqual,
    }
}

// Keep float-only temporaries out of the recursive shared renderer's frame.
fn raise_float_expression(
    term: &crate::kernel::KernelTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    use crate::kernel::KernelTermNode as Node;
    let recurse = |term| raise_kernel_term(term, parameter_binding, state, bound_variables);
    Some(match term.node() {
        Node::FloatConvert {
            destination,
            operand,
            ..
        } => synthesize_observation_operand(recurse(operand)?, *destination)?,
        Node::FloatNegate { operand } => SyntaxTerm::Negate(Box::new(recurse(operand)?)),
        Node::FloatBinary {
            operator,
            arguments,
        } => {
            let left = Box::new(recurse(&arguments[0])?);
            let right = Box::new(recurse(&arguments[1])?);
            match operator {
                crate::kernel::FloatBinaryOperator::Add => SyntaxTerm::Add(left, right),
                crate::kernel::FloatBinaryOperator::Subtract => SyntaxTerm::Subtract(left, right),
                crate::kernel::FloatBinaryOperator::Multiply => SyntaxTerm::Multiply(left, right),
                crate::kernel::FloatBinaryOperator::Divide => SyntaxTerm::Divide(left, right),
            }
        }
        Node::FloatCall(call) => raise_call(
            &call.name,
            &call.arguments,
            parameter_binding,
            state,
            bound_variables,
        )?,
        Node::FloatCompare {
            operator,
            arguments,
            ..
        } => proposition_bool_value(SyntaxProposition::Comparison {
            left: recurse(&arguments[0])?,
            operator: surface_float_comparison_operator(*operator),
            right: recurse(&arguments[1])?,
        })
        .ok()?,
        Node::FloatClassify {
            classification,
            operand,
            ..
        } => proposition_bool_value(SyntaxProposition::FloatClassification {
            expression: recurse(operand)?,
            classification: surface_float_classification(*classification),
        })
        .ok()?,
        _ => unreachable!("float expression dispatch"),
    })
}

/// The shared term-to-surface boundary. Arithmetic and calls have common
/// children; the legacy leaf dispatch is temporary and never projects away
/// part of a value. Fold bodies retain their typed lexical scope.
pub(super) fn raise_kernel_term(
    term: &crate::kernel::KernelTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    use crate::kernel::{KernelTermNode as Node, KernelType};
    // A program parameter changes the argument carrier, not its spelling.
    // Peel that envelope without another recursive renderer frame.
    let term = match term.node() {
        Node::ProgramParameter { operand } => operand,
        _ => term,
    };
    let category = if term.ty() == &KernelType::Integer {
        "integer"
    } else {
        "function-call"
    };
    let _frame = SurfaceSynthesisFrame::enter(category)?;
    if let Node::BoolIf {
        arguments: [zero_test, if_true, if_false],
    } = term.node()
        && matches!(if_true.node(), Node::BoolLiteral(false))
        && matches!(if_false.node(), Node::BoolLiteral(true))
        && let Some(read) = synthesize_boolean_cell_read(
            crate::kernel::BooleanOperandView::Shared(zero_test),
            parameter_binding,
            state,
            bound_variables,
        )
    {
        return Some(read);
    }
    // The general renderer has large temporaries for unrelated Surface forms.
    // Keep them out of each recursive integer-operation frame, so the existing
    // depth budget can refuse a shared DAG before the thread stack runs out.
    if let Node::IntegerOperation {
        operator,
        arguments,
    } = term.node()
    {
        return raise_integer_operation(
            *operator,
            arguments,
            parameter_binding,
            state,
            bound_variables,
        );
    }
    raise_kernel_term_dispatch(term, parameter_binding, state, bound_variables)
}

// Pointer-value equality can name full pointers even when their addresses
// coincide. Address and offset comparisons retain their own operand types.
fn raise_pointer_comparison(
    term: &crate::kernel::KernelTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    use crate::kernel::KernelTermNode as Node;
    let (left, right) = match term.node() {
        Node::PointerEqual(pair) => {
            let [left, right] = pair.arguments();
            let shared_address =
                left.node().address == right.node().address && !left.same_source_payload(right);
            let operand = |value: &crate::kernel::SharedPointer| {
                if let Some(name) = pointer_names::shared_name(value) {
                    return Some(SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                        name.into(),
                    )));
                }
                if shared_address {
                    return synthesize_pointer_equality_operand(
                        &value.export().ok()?,
                        parameter_binding,
                        state,
                        bound_variables,
                    );
                }
                synthesize_pointer_equality_address(
                    &value.node().address.export().ok()?,
                    value.node().program_type,
                    parameter_binding,
                    state,
                    bound_variables,
                )
            };
            let left = operand(left)?;
            let right = operand(right)?;
            if shared_address && left == right {
                crate::surface::proof::raise_lower_audit::note_reason(|| {
                    "pointer equality: its operands share an address but have no distinct names"
                        .to_string()
                });
                return None;
            }
            (left, right)
        }
        Node::AddressEqual { arguments, .. } => {
            let left = arguments[0].export().ok()?;
            let right = arguments[1].export().ok()?;
            // As the condition form above: a pointer equality is `p == q`.
            let pointer = synthesize_surface_pointer_expression;
            (
                pointer(&left, parameter_binding, state, bound_variables)?,
                pointer(&right, parameter_binding, state, bound_variables)?,
            )
        }
        Node::AddressOffsetEqual { arguments } => (
            synthesize_surface_pointer_offset(
                &AddressOffset::try_from_shared(arguments[0].clone()).ok()?,
                parameter_binding,
                state,
                bound_variables,
            )?,
            synthesize_surface_pointer_offset(
                &AddressOffset::try_from_shared(arguments[1].clone()).ok()?,
                parameter_binding,
                state,
                bound_variables,
            )?,
        ),
        _ => return None,
    };
    proposition_bool_value(SyntaxProposition::Comparison {
        left,
        operator: ComparisonOperator::Equal,
        right,
    })
    .ok()
}

// Definedness names the written operation, even when a local holds its
// result. Keep its children shared and preserve the supported overflow profile.
fn raise_shared_overflow(
    format: MachineIntegerType,
    operation: OverflowOperation,
    arguments: &[crate::kernel::KernelTerm; 2],
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    if !matches!(
        format,
        MachineIntegerType::Int32 | MachineIntegerType::Int64
    ) || !matches!(
        operation,
        OverflowOperation::Add | OverflowOperation::Subtract | OverflowOperation::Multiply
    ) {
        return None;
    }
    let left = Box::new(raise_kernel_term(
        &arguments[0],
        parameter_binding,
        state,
        bound_variables,
    )?);
    let right = Box::new(raise_kernel_term(
        &arguments[1],
        parameter_binding,
        state,
        bound_variables,
    )?);
    let expression = match operation {
        OverflowOperation::Add => SyntaxTerm::Add(left, right),
        OverflowOperation::Subtract => SyntaxTerm::Subtract(left, right),
        OverflowOperation::Multiply => SyntaxTerm::Multiply(left, right),
        _ => unreachable!("supported overflow operation"),
    };
    proposition_bool_value(SyntaxProposition::Not(Box::new(
        SyntaxProposition::Defined { expression },
    )))
    .ok()
}

// Read spelling keeps the native boundary's selection order and state
// equality, but compares the common address without exporting its index DAG.
fn raise_algebraic_read(
    term: &crate::kernel::KernelTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    use crate::kernel::{AlgebraicTermNode, KernelTermNode, KernelType};
    let (KernelType::Algebraic(ty), KernelTermNode::AlgebraicRead(read)) = (term.ty(), term.node())
    else {
        return None;
    };
    let (point, address) = read.parts();
    if point.read_version_id().is_some() {
        return synthesize_point_algebraic_read(
            ty,
            point,
            &address.export().ok()?,
            parameter_binding,
            state,
            bound_variables,
        );
    }
    let memory = point.shared_memory();
    let same_address = |pointer: &Address| address.syntax_equal(pointer.shared());
    if let Some((parameter, _)) = parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
        .find(|(_, argument)| {
            matches!(argument, ProgramExpression::Value(ProgramValue::Pointer(value))
                if same_address(value.address()))
        })
    {
        return Some(SyntaxTerm::ProgramExpression(ProgramExpression::Load(
            Box::new(ProgramExpression::Variable(
                crate::surface::surface_parameter_binding(parameter.binding_name()),
            )),
        )));
    }
    let held_at = |state: &ExecutionState| {
        let (name, _, _) = state.locals().held_value_locals().find(|(_, _, slot)| {
            crate::instrumentation::record_deterministic_work(1);
            same_address(slot)
        })?;
        let Some(ProgramValue::Parameter(held)) = state.held_local_value(name) else {
            return None;
        };
        let AlgebraicTermNode::MemoryLoad {
            point: held_memory,
            pointer,
        } = &held.node
        else {
            return None;
        };
        (ty == &held.algebraic_type
            && memory == held_memory.shared_memory()
            && same_address(pointer))
        .then(|| SyntaxTerm::ProgramExpression(ProgramExpression::Variable(name.clone())))
    };
    held_at(state).or_else(|| {
        SYNTHESIS_RECORDED_POINTS.with(|slot| {
            let slot = slot.borrow();
            let points = slot.as_ref()?;
            let (selector, recorded) = if point.id().is_some() {
                points.point_naming_read(point)
            } else {
                points
                    .point_reading_memory(memory)
                    .or_else(|| points.point_reading_load(point, &address.export().ok()?))
            }?;
            Some(SyntaxTerm::At {
                selector: selector.clone(),
                expression: Box::new(held_at(recorded)?),
            })
        })
    })
}

// Constructor fields retain their existing spelling policy independently of
// call arguments: pointer fields can need a root-view cast, and non-int32
// scalar fields currently require a named variable.
fn raise_constructor_field(
    term: &crate::kernel::KernelTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    use crate::kernel::{KernelTermNode as Node, KernelType};
    let term = match term.node() {
        Node::ProgramParameter { operand } => operand,
        _ => term,
    };
    if matches!(term.node(), Node::MachineLiteral(_))
        || term.ty() == &KernelType::Bool
            && matches!(term.node(), Node::Variable(_) | Node::BoolLiteral(_))
    {
        return raise_kernel_term(term, parameter_binding, state, bound_variables);
    }
    if matches!(term.ty(), KernelType::Algebraic(_)) {
        return raise_kernel_term(term, parameter_binding, state, bound_variables);
    }
    if let Some(ProgramValue::Pointer(pointer)) = term.old_pointer_value() {
        if pointer.is_wide() {
            return slices::raise_slice(pointer, parameter_binding, state, bound_variables);
        }
        return raise_constructor_pointer(pointer, parameter_binding, state, bound_variables);
    }
    if term.ty() == &KernelType::Integer {
        return raise_kernel_term(term, parameter_binding, state, bound_variables)
            .map(integer_typed_expression);
    }
    if term.ty() == &KernelType::Program(ProgramType::Int32) {
        return raise_kernel_term(term, parameter_binding, state, bound_variables);
    }
    let variable = match (term.ty(), term.node()) {
        (
            KernelType::Program(
                ProgramType::Bool
                | ProgramType::Int8
                | ProgramType::UInt8
                | ProgramType::Int16
                | ProgramType::UInt16
                | ProgramType::UInt32
                | ProgramType::Int64
                | ProgramType::UInt64,
            ),
            Node::Variable(variable),
        ) => *variable,
        _ => match term.old_boolean_value()? {
            ProgramValue::Bool(OldMachineTerm::Variable(variable)) => *variable,
            _ => return None,
        },
    };
    bound_variables
        .get(&variable)
        .map(|name| SyntaxTerm::ProgramExpression(ProgramExpression::Variable(name.clone().into())))
        .or_else(|| {
            synthesize_surface_bitvector(
                &OldMachineTerm::Variable(variable),
                parameter_binding,
                state,
                bound_variables,
            )
        })
}

fn raise_constructor_pointer(
    pointer: &crate::kernel::Pointer,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    synthesize_surface_pointer_expression(pointer, parameter_binding, state, bound_variables)
        .or_else(|| synthesize_loaded_pointer_value(pointer, parameter_binding, state))
        .map(|expression| {
            // Constructors implicitly retag object pointers
            // without widening their views. A checked root view
            // is the byte view a character conversion forms
            // (C11 6.3.2.3p7), retagged to `void *`; adding it to
            // a saved narrow view would change the value.
            if pointer.program_type() == ProgramType::VoidPointer
                && pointer.bounds_are_known()
                && pointer.bounds().is_none()
            {
                let cast = |operand: SyntaxTerm, target_type| SyntaxTerm::CUnary {
                    lowered: ProgramExpression::Cast {
                        expression: Box::new(ProgramExpression::Value(ProgramValue::Pointer(
                            pointer.clone(),
                        ))),
                        target_type,
                        integer_mode: crate::kernel::IntegerCastMode::Standard,
                        pointee_struct: None,
                        pointee_struct_size: None,
                        pointee_volatile: false,
                        pointee_constant: false,
                        explicit_qualification: false,
                    },
                    operand: Box::new(operand),
                };
                cast(
                    cast(expression, ProgramType::UInt8Pointer),
                    ProgramType::VoidPointer,
                )
            } else {
                expression
            }
        })
}

fn raise_integer_operation(
    operator: crate::kernel::KernelIntegerOperator,
    arguments: &[crate::kernel::KernelTerm],
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    use crate::kernel::KernelIntegerOperator as Op;
    let recurse = |term| raise_kernel_term(term, parameter_binding, state, bound_variables);
    let mut arguments = arguments
        .iter()
        .map(recurse)
        .collect::<Option<Vec<_>>>()?
        .into_iter();
    let left = arguments.next()?;
    Some(match operator {
        Op::Negate => SyntaxTerm::Negate(Box::new(integer_typed_expression(left))),
        Op::Add => SyntaxTerm::Add(Box::new(left), Box::new(arguments.next()?)),
        Op::Subtract => SyntaxTerm::Subtract(Box::new(left), Box::new(arguments.next()?)),
        Op::Multiply => SyntaxTerm::Multiply(Box::new(left), Box::new(arguments.next()?)),
        Op::TruncatingQuotient | Op::TruncatingRemainder => SyntaxTerm::Call {
            name: if operator == Op::TruncatingQuotient {
                "truncating_quotient"
            } else {
                "truncating_remainder"
            }
            .into(),
            arguments: vec![left, arguments.next()?],
        },
    })
}

// A printed comparison operand or conditional arm can reparse arithmetic as
// Integer. Keep the machine context of the bounded operation there.
fn spell_bounded_wide_arithmetic_operand(
    term: &crate::kernel::KernelTerm,
    expression: SyntaxTerm,
) -> Option<SyntaxTerm> {
    use crate::kernel::KernelTermNode as Node;
    if let Node::MachineBinary {
        format: format @ (MachineIntegerType::Int64 | MachineIntegerType::UInt64),
        operator,
        arguments,
    } = term.node()
        && match operator {
            MachineBinaryOp::Add | MachineBinaryOp::Subtract | MachineBinaryOp::Multiply => {
                matches!(
                    arguments.each_ref().map(|child| child.node()),
                    [
                        Node::Variable(_),
                        Node::Variable(_) | Node::MachineLiteral(_)
                    ] | [Node::MachineLiteral(_), Node::Variable(_)]
                ) && (*format == MachineIntegerType::UInt64
                    || arguments
                        .iter()
                        .all(|child| matches!(child.node(), Node::Variable(_))))
            }
            MachineBinaryOp::Divide | MachineBinaryOp::Remainder => {
                *format == MachineIntegerType::UInt64
                    && matches!(arguments[0].node(), Node::Variable(_))
                    && (matches!(arguments[1].node(), Node::Variable(_))
                        || crate::kernel::MachineOperandView::Shared(&arguments[1])
                            .uint64_constant()
                            .is_some_and(|divisor| divisor != 0))
            }
            _ => false,
        }
        && matches!(
            expression,
            SyntaxTerm::Add(..)
                | SyntaxTerm::Subtract(..)
                | SyntaxTerm::Multiply(..)
                | SyntaxTerm::Divide(..)
                | SyntaxTerm::Remainder(..)
        )
    {
        synthesize_observation_operand(expression, format.program_type())
    } else {
        Some(expression)
    }
}

fn raise_kernel_term_dispatch(
    term: &crate::kernel::KernelTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    use crate::kernel::{KernelTermNode as Node, KernelType};
    let recurse = |term| raise_kernel_term(term, parameter_binding, state, bound_variables);
    if matches!(
        term.node(),
        Node::MachineBinary { .. }
            | Node::MachineUnary { .. }
            | Node::MachineCast { .. }
            | Node::MachineIf { .. }
    ) && let Some(named) =
        synthesize_named_integer_local(state, state.locals().names_holding_kernel_integer(term))
    {
        return Some(named);
    }
    Some(match term.node() {
        Node::Fold(fold) => folds::raise_fold(fold, parameter_binding, state, bound_variables)?,
        Node::Match(matched) => {
            matches::raise_match(matched, parameter_binding, state, bound_variables)?
        }
        Node::Constructor(constructor) => SyntaxTerm::AlgebraicConstructor {
            algebraic_type: surface_algebraic_type(&constructor.algebraic_type)?,
            variant: constructor.variant.clone(),
            arguments: constructor
                .fields
                .iter()
                .map(|field| {
                    raise_constructor_field(field, parameter_binding, state, bound_variables)
                })
                .collect::<Option<Vec<_>>>()?,
        },
        Node::AlgebraicRead(_) => {
            raise_algebraic_read(term, parameter_binding, state, bound_variables)?
        }
        Node::Variable(_) if matches!(term.ty(), KernelType::Algebraic(_)) => {
            // Variable naming uses a bounded typed descriptor, not a tree export.
            synthesize_surface_algebraic(
                term.algebraic_native_term()?,
                parameter_binding,
                state,
                bound_variables,
            )?
        }
        Node::IntegerLiteral(value) if value.sign() == num_bigint::Sign::Minus => {
            SyntaxTerm::Negate(Box::new(SyntaxTerm::IntegerLiteral((-value).to_string())))
        }
        Node::IntegerLiteral(value) => SyntaxTerm::IntegerLiteral(value.to_string()),
        Node::Variable(variable) if term.ty() == &KernelType::Integer => {
            match folds::binder_name(true, *variable)
                .or_else(|| bound_variables.get(variable).cloned())
                .or_else(|| proof_binder_name(*variable))
                // A name the loop phase gives a variable it binds, such as
                // the head's pass count `iterations`.
                .or_else(|| {
                    SYNTHESIS_BINDER_NAMES.with(|slot| {
                        slot.borrow()
                            .as_ref()
                            .and_then(|names| names.get(variable).cloned())
                    })
                }) {
                Some(name) => name.reference(),
                // A loop's pass count past the loop.
                None => SyntaxTerm::Binding(crate::surface::loop_iterations_spelling(
                    SYNTHESIS_RECORDED_POINTS
                        .with(|slot| slot.borrow().as_ref()?.loop_naming_iterations(*variable))?,
                )),
            }
        }
        Node::AlgebraicIf { arguments } => raise_algebraic_if(arguments, recurse)?,
        Node::IntegerIf { arguments } => SyntaxTerm::If {
            condition: Box::new(raise_value_if_guard(&arguments[0], recurse(&arguments[0])?)),
            then_branch: Box::new(integer_typed_expression(recurse(&arguments[1])?)),
            else_branch: Box::new(integer_typed_expression(recurse(&arguments[2])?)),
        },
        Node::IntegerOperation { .. } => unreachable!("integer operation dispatch"),
        Node::AlgebraicCall(call) => raise_call(
            &call.name,
            &call.arguments,
            parameter_binding,
            state,
            bound_variables,
        )?,
        Node::Call { name, arguments } => {
            let call = raise_call(name, arguments, parameter_binding, state, bound_variables)?;
            // The root may read a call's word at the other signedness. Its
            // declaration alone cannot recover that selected interpretation.
            // Native 128-bit calls refuse even identity casts, so their
            // unchanged declaration remains the supported spelling.
            if let KernelType::Program(ty) = term.ty()
                && MachineIntegerType::from_program_type(*ty)
                    .is_some_and(|format| format.format().bits() <= 64)
            {
                synthesize_observation_operand(call, *ty)?
            } else {
                call
            }
        }
        Node::BoolLiteral(value) => bool_literal(*value),
        Node::BoolIf { arguments } | Node::MachineIf { arguments } => {
            let arm = |index: usize| {
                let term = &arguments[index];
                let expression = spell_bounded_wide_arithmetic_operand(term, recurse(term)?)?;
                // The signed 64-bit reading of an unsigned variable retains
                // the word, so its name needs the arm's type on the surface.
                if term.ty() == &KernelType::Program(ProgramType::Int64)
                    && let Node::Variable(variable) = term.node()
                    && !bound_variables.contains_key(variable)
                    && folds::binder_name(false, *variable).is_none()
                    && variable_spells_uint64(*variable, parameter_binding, state)
                {
                    synthesize_observation_operand(expression, ProgramType::Int64)
                } else {
                    Some(expression)
                }
            };
            SyntaxTerm::If {
                condition: Box::new(bool_truth(recurse(&arguments[0])?)),
                then_branch: Box::new(arm(1)?),
                else_branch: Box::new(arm(2)?),
            }
        }
        Node::BoolEqual { arguments } => proposition_bool_value(SyntaxProposition::Comparison {
            left: recurse(&arguments[0])?,
            operator: ComparisonOperator::Equal,
            right: recurse(&arguments[1])?,
        })
        .ok()?,
        Node::IntegerCompare {
            operator,
            arguments,
        } => {
            use crate::kernel::IntegerComparisonOperator as C;
            proposition_bool_value(SyntaxProposition::Comparison {
                left: integer_typed_expression(recurse(&arguments[0])?),
                operator: match operator {
                    C::Equal => ComparisonOperator::Equal,
                    C::NotEqual => ComparisonOperator::NotEqual,
                    C::LessThan => ComparisonOperator::LessThan,
                    C::LessEqual => ComparisonOperator::LessEqual,
                    C::GreaterThan => ComparisonOperator::GreaterThan,
                    C::GreaterEqual => ComparisonOperator::GreaterEqual,
                },
                right: recurse(&arguments[1])?,
            })
            .ok()?
        }
        Node::BoolCompare {
            format,
            relation,
            arguments,
        } => {
            // Wide equality reads unsigned literals as the same words. Keep
            // their payloads even beside a variable: signed casts change literals.
            use crate::kernel::MachineOperandView as V;
            let wide_equality = *relation == CompareRelation::Equal && format.format().bits() == 64;
            let unsigned_literal = wide_equality
                && arguments.iter().any(|term| {
                    V::Shared(term)
                        .literal()
                        .is_some_and(|value| value.uint64_as_const().is_some())
                });
            let unsigned_cast = |operand: V<'_>| {
                operand.cast().is_some_and(|(spelling, _, _, child)| {
                    matches!(
                        spelling,
                        MachineCastSpelling::UInt64FromInt32 | MachineCastSpelling::UInt64From32
                    ) && (child.variable().is_some() || child.literal().is_some())
                        || (spelling == MachineCastSpelling::UInt64FromInt64
                            && child.variable().is_some())
                })
            };
            let operands = arguments.each_ref().map(V::Shared);
            // Equality compares bits. Casting to the Int64 filing type
            // would change or erase the unsigned cast.
            let unsigned_word = wide_equality
                && operands.iter().copied().any(unsigned_cast)
                && operands
                    .iter()
                    .copied()
                    .all(|operand| unsigned_cast(operand) || operand.variable().is_some());
            let operand = |term| {
                let expression = spell_bounded_wide_arithmetic_operand(term, recurse(term)?)?;
                if unsigned_literal || (unsigned_word && unsigned_cast(V::Shared(term))) {
                    Some(expression)
                } else {
                    let ty = if unsigned_word {
                        ProgramType::UInt64
                    } else {
                        format.program_type()
                    };
                    synthesize_observation_operand(expression, ty)
                }
            };
            proposition_bool_value(SyntaxProposition::Comparison {
                left: operand(&arguments[0])?,
                operator: match relation {
                    CompareRelation::Equal => ComparisonOperator::Equal,
                    CompareRelation::LessThan => ComparisonOperator::LessThan,
                    CompareRelation::LessEqual => ComparisonOperator::LessEqual,
                    CompareRelation::GreaterThan => ComparisonOperator::GreaterThan,
                    CompareRelation::GreaterEqual => ComparisonOperator::GreaterEqual,
                },
                right: operand(&arguments[1])?,
            })
            .ok()?
        }
        // Offset spelling still uses its existing address context at the
        // explicit Surface boundary; no new standalone offset syntax.
        Node::AlgebraicEqual { arguments } => {
            proposition_bool_value(SyntaxProposition::Comparison {
                left: recurse(&arguments[0])?,
                operator: ComparisonOperator::Equal,
                right: recurse(&arguments[1])?,
            })
            .ok()?
        }
        Node::BoolOverflow {
            format,
            operation,
            arguments,
        } => raise_shared_overflow(
            *format,
            *operation,
            arguments,
            parameter_binding,
            state,
            bound_variables,
        )?,
        Node::PointerEqual(_) | Node::AddressEqual { .. } | Node::AddressOffsetEqual { .. } => {
            raise_pointer_comparison(term, parameter_binding, state, bound_variables)?
        }
        Node::Variable(variable) if term.ty() == &KernelType::Bool => synthesize_surface_bool(
            &OldConditionTerm::Variable(*variable),
            parameter_binding,
            state,
            bound_variables,
        )?,
        Node::BoolCast {
            destination,
            operand,
        } => synthesize_observation_operand(recurse(operand)?, destination.program_type())?,
        Node::IntegerToMachine {
            destination,
            operand,
        } => SyntaxTerm::Call {
            name: integer_conversion_name(*destination).into(),
            arguments: vec![recurse(operand)?],
        },
        Node::MachineObservation { format, operand } => {
            let expression = recurse(operand)?;
            SyntaxTerm::Call {
                name: "to_integer".into(),
                arguments: vec![match format {
                    // Narrow loads and conversions already spell their
                    // extended carrier. Adding a narrowing or promotion
                    // cast changes scoped observation nodes.
                    crate::kernel::MachineIntegerType::Int8
                    | crate::kernel::MachineIntegerType::UInt8
                    | crate::kernel::MachineIntegerType::Int16
                    | crate::kernel::MachineIntegerType::UInt16 => expression,
                    _ => synthesize_observation_operand(expression, format.program_type())?,
                }],
            }
        }
        Node::ProgramParameter { .. } => unreachable!("parameter envelope was peeled"),
        Node::PointerCall { call, .. } => recurse(call)?,
        // An array argument is its pointer, spelled as any pointer argument
        // is (a proof name, or `0` for null), read at the view's state.
        // A null array is formed at no state; it is the literal `0`.
        Node::ArrayReference { pointer, .. }
            if matches!(
                pointer.old_pointer_value(),
                Some(ProgramValue::Pointer(value)) if value.address() == &Address::null()
            ) =>
        {
            SyntaxTerm::IntegerLiteral("0".into())
        }
        Node::ArrayReference { point, pointer, .. } => {
            let raise = |selected: &ExecutionState| {
                raise_call_argument(pointer, parameter_binding, selected, bound_variables)
            };
            synthesize_at_read_origin(point, state, raise)?
        }

        Node::PointerRead { value, .. }
        | Node::PointerArithmetic { value, .. }
        | Node::Pointer(value) => {
            if let Some(name) = pointer_names::shared_name(value) {
                SyntaxTerm::ProgramExpression(ProgramExpression::Variable((name).into()))
            } else {
                synthesize_surface_value(term.old_pointer_value()?, parameter_binding, state)?
            }
        }
        Node::WrittenMachine(input) => {
            if input.format().format().bits() < 32 {
                return None;
            }
            synthesize_surface_bitvector(input.value(), parameter_binding, state, bound_variables)?
        }
        Node::MachineObservationInput {
            format,
            observation,
            ..
        } => {
            if format.format().bits() < 32 {
                return None;
            }
            synthesize_surface_bitvector(
                observation.value(),
                parameter_binding,
                state,
                bound_variables,
            )?
        }
        Node::ImportedScalar(input) => match term.ty() {
            KernelType::Program(ProgramType::Bool) => synthesize_surface_bool(
                &OldConditionTerm::truth_of_bool_word(input.value()),
                parameter_binding,
                state,
                bound_variables,
            )?,
            KernelType::Program(ty)
                if MachineIntegerType::from_program_type(*ty)
                    .is_some_and(|format| format.format().bits() >= 32) =>
            {
                synthesize_surface_bitvector(
                    input.value(),
                    parameter_binding,
                    state,
                    bound_variables,
                )?
            }
            _ => return None,
        },
        Node::ObservedPointer(value) => recurse(value.source())?,
        Node::CallArgument(argument) => synthesize_legacy_call_argument(
            argument.value(),
            parameter_binding,
            state,
            bound_variables,
        )?,
        Node::NativeDescriptor(_) | Node::ObservedArgument(_) => synthesize_legacy_call_argument(
            term.written_argument()?,
            parameter_binding,
            state,
            bound_variables,
        )?,
        Node::FloatCompare { .. }
        | Node::FloatClassify { .. }
        | Node::FloatConvert { .. }
        | Node::FloatNegate { .. }
        | Node::FloatBinary { .. }
        | Node::FloatCall(_) => {
            raise_float_expression(term, parameter_binding, state, bound_variables)?
        }
        Node::FloatRead(read) => {
            let KernelType::Program(value_type) = term.ty() else {
                unreachable!("float read type");
            };
            raise_float_read(read, *value_type, parameter_binding, state, bound_variables)?
        }
        Node::FloatLiteral { .. } => SyntaxTerm::ProgramExpression(ProgramExpression::Value(
            crate::kernel::KernelTermExport::float(term).ok()?,
        )),
        Node::MachineLiteral(literal) => {
            let KernelType::Program(ty) = term.ty() else {
                return None;
            };
            SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                literal.value_at(MachineIntegerType::from_program_type(*ty)?),
            ))
        }
        Node::MachineBinary {
            format,
            operator,
            arguments,
        } => {
            let left = Box::new(recurse(&arguments[0])?);
            let mut right = Box::new(recurse(&arguments[1])?);
            if *format == MachineIntegerType::UInt32
                && matches!(
                    operator,
                    MachineBinaryOp::Divide | MachineBinaryOp::Remainder
                )
            {
                right = Box::new(synthesize_uint32_operand(*right)?);
            }
            match operator {
                MachineBinaryOp::Add => SyntaxTerm::Add(left, right),
                MachineBinaryOp::Subtract => SyntaxTerm::Subtract(left, right),
                MachineBinaryOp::Multiply => SyntaxTerm::Multiply(left, right),
                MachineBinaryOp::Divide => SyntaxTerm::Divide(left, right),
                MachineBinaryOp::Remainder => SyntaxTerm::Remainder(left, right),
                MachineBinaryOp::ShiftLeft => SyntaxTerm::ShiftLeft(left, right),
                MachineBinaryOp::ShiftRight => SyntaxTerm::ShiftRight(left, right),
                MachineBinaryOp::BitwiseAnd => SyntaxTerm::BitwiseAnd(left, right),
                MachineBinaryOp::BitwiseOr => SyntaxTerm::BitwiseOr(left, right),
                MachineBinaryOp::BitwiseXor => SyntaxTerm::BitwiseXor(left, right),
            }
        }
        Node::MachineUnary { operand, .. } => SyntaxTerm::BitwiseNot(Box::new(recurse(operand)?)),
        Node::IntegerAddress { .. } | Node::ThreadHandle(_) => {
            let expression = synthesize_surface_bitvector(
                term.machine_conversion_leaf()?,
                parameter_binding,
                state,
                bound_variables,
            )?;
            if term.ty() == &crate::kernel::KernelType::Program(ProgramType::Int64) {
                synthesize_observation_operand(expression, ProgramType::Int64)?
            } else {
                expression
            }
        }
        Node::MemoryLoad { .. } => {
            let read = term.machine_read_leaf()?;
            match term.ty() {
                KernelType::Program(value_type @ (ProgramType::Int64 | ProgramType::UInt64))
                    if matches!(
                        read,
                        OldMachineTerm::MemoryLoad(_, _, crate::kernel::LoadKind::Bits64)
                    ) =>
                {
                    synthesize_typed_word_read(
                        read,
                        *value_type,
                        parameter_binding,
                        state,
                        bound_variables,
                    )?
                }
                _ => synthesize_surface_bitvector(read, parameter_binding, state, bound_variables)?,
            }
        }
        Node::Variable(variable)
            if let KernelType::Program(ty @ (ProgramType::Float32 | ProgramType::Float64)) =
                term.ty() =>
        {
            if let Some(name) = folds::binder_name(false, *variable)
                .or_else(|| bound_variables.get(variable).cloned())
                .or_else(|| proof_binder_name(*variable))
            {
                SyntaxTerm::ProgramExpression(ProgramExpression::Variable(name.into()))
            } else {
                let (parameter, argument) =
                    parameter_binding.naming?.float_source(*ty, *variable)?;
                let name = crate::surface::surface_parameter_binding(parameter.binding_name());
                let expression = program_operand(ProgramExpression::Variable(name.clone()));
                if parameter_names_its_argument(&name, argument, state) {
                    expression
                } else {
                    SyntaxTerm::Old(Box::new(expression))
                }
            }
        }
        Node::Variable(variable) => synthesize_surface_bitvector(
            &OldMachineTerm::Variable(*variable),
            parameter_binding,
            state,
            bound_variables,
        )?,
        Node::MachineCast {
            encoding,
            source,
            destination,
            operand,
        } => {
            let mut expression = recurse(operand)?;
            if *encoding == MachineCastSpelling::Generic
                && crate::kernel::is_narrow_widening32(*source, *destination)
            {
                if *destination == MachineIntegerType::UInt32 {
                    synthesize_uint32_operand(expression)?
                } else {
                    synthesize_int32_operand(expression)?
                }
            } else {
                if matches!(
                    encoding,
                    MachineCastSpelling::Int64From32
                        | MachineCastSpelling::Int64FromUInt32
                        | MachineCastSpelling::UInt64From32
                        | MachineCastSpelling::UInt64FromInt32
                ) {
                    expression = if matches!(
                        encoding,
                        MachineCastSpelling::Int64FromUInt32 | MachineCastSpelling::UInt64From32
                    ) {
                        synthesize_uint32_operand(expression)?
                    } else {
                        synthesize_int32_operand(expression)?
                    };
                }
                SyntaxTerm::CUnary {
                    operand: Box::new(expression),
                    lowered: ProgramExpression::Cast {
                        expression: Box::new(ProgramExpression::Value(int32(0))),
                        target_type: destination.program_type(),
                        integer_mode: if *encoding == MachineCastSpelling::UInt32From64 {
                            crate::kernel::IntegerCastMode::Standard
                        } else {
                            crate::kernel::IntegerCastMode::CConversion
                        },
                        pointee_struct: None,
                        pointee_struct_size: None,
                        pointee_volatile: false,
                        pointee_constant: false,
                        explicit_qualification: false,
                    },
                }
            }
        }
    })
}

fn integer_conversion_name(format: crate::kernel::MachineIntegerType) -> &'static str {
    use crate::kernel::MachineIntegerType::*;
    match format {
        Int8 => "to_int8",
        UInt8 => "to_uint8",
        Int16 => "to_int16",
        UInt16 => "to_uint16",
        Int32 => "to_int32",
        UInt32 => "to_uint32",
        Int64 => "to_int64",
        UInt64 => "to_uint64",
        Int128 => "to_int128",
        UInt128 => "to_uint128",
    }
}

/// Keep the observation's interpretation inside its program point selector.
fn synthesize_observation_operand(
    expression: SyntaxTerm,
    format: ProgramType,
) -> Option<SyntaxTerm> {
    Some(match expression {
        SyntaxTerm::At {
            selector,
            expression,
        } => SyntaxTerm::At {
            selector,
            expression: Box::new(synthesize_observation_operand(*expression, format)?),
        },
        SyntaxTerm::Old(expression) => SyntaxTerm::Old(Box::new(synthesize_observation_operand(
            *expression,
            format,
        )?)),
        expression => SyntaxTerm::CUnary {
            operand: Box::new(expression),
            // CUnary's Surface operand is authoritative. A C fragment
            // would discard resource fields and scoped binding information.
            lowered: ProgramExpression::Cast {
                expression: Box::new(ProgramExpression::Value(int32(0))),
                target_type: format,
                integer_mode: crate::kernel::IntegerCastMode::CConversion,
                pointee_struct: None,
                pointee_struct_size: None,
                pointee_volatile: false,
                pointee_constant: false,
                explicit_qualification: false,
            },
        },
    })
}

/// A `uint32` order spelled as a comparison of `uint32` operands.
///
/// The kernel's 32-bit words carry no signedness, so each operand is spelled
/// so that it reads as `uint32`: constants and `uint32` locals keep their
/// direct spellings, and computed operands and signed locals receive an
/// explicit `uint32` cast. The comparison lowers back to the same `uint32`
/// order. A comparison with a state-relative operand has no spelling
/// here.
fn synthesize_unsigned_comparison(
    condition: &OldConditionTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxProposition> {
    let OldConditionTerm::Compare {
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
        CompareRelation::LessThan => ComparisonOperator::LessThan,
        CompareRelation::LessEqual => ComparisonOperator::LessEqual,
        CompareRelation::GreaterThan => ComparisonOperator::GreaterThan,
        CompareRelation::GreaterEqual => ComparisonOperator::GreaterEqual,
        CompareRelation::Equal => return None,
    };
    let (left, right) = (left.as_ref(), right.as_ref());
    // The `uint32` local holding the operand, named directly: a signed local
    // can hold the same bits, and its name would make the comparison signed.
    let operand = |term: &OldMachineTerm| match term.as_const() {
        Some(_) => Some(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
            ProgramValue::UInt32(term.clone()),
        ))),
        None => state
            .locals()
            .names_holding_integer(term)
            .find(|name| {
                !name.is_named("result")
                    && *name != &crate::kernel::CONTRACT_RESULT
                    && state.locals().get(*name).is_some_and(|value| {
                        value.program_type() == crate::kernel::ProgramType::UInt32
                            && value
                                .native_payload()
                                .is_none_or(|native| matches!(native, ProgramValue::UInt32(_)))
                    })
            })
            .map(|name| {
                synthesize_call_capture(state, name).unwrap_or_else(|| {
                    SyntaxTerm::ProgramExpression(ProgramExpression::Variable(surface_local_name(
                        name,
                    )))
                })
            })
            .or_else(|| {
                let expression =
                    synthesize_surface_bitvector(term, parameter_binding, state, bound_variables)?;
                // A state-relative operand is left to the diagnostic
                // renderer, which spells it in its state, preserving
                // loop-ranking observations and refusal diagnostics.
                // Division/remainder still cast within their own state
                // when reconstructing those operations.
                if matches!(expression, SyntaxTerm::At { .. } | SyntaxTerm::Old(_)) {
                    return None;
                }
                synthesize_uint32_operand(expression)
            }),
    };
    Some(SyntaxProposition::Comparison {
        left: operand(left)?,
        operator,
        right: operand(right)?,
    })
}

/// One argument of a declared resource, spelled by the value it carries.
fn synthesize_surface_resource_argument(
    argument: &crate::kernel::AlgebraicValue,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    use crate::kernel::AlgebraicValue as A;
    match argument {
        // A local's storage is spelled by the local, `&pool`, as a memory
        // range's base is.
        A::Program(ProgramValue::Pointer(pointer))
            if let Some(name) = state.locals().name_for_slot(pointer.address()) =>
        {
            let object = ProgramExpression::Variable(surface_local_name(name));
            Some(SyntaxTerm::ProgramExpression(
                if state.locals().array_object_element_type(name).is_some() {
                    object
                } else {
                    ProgramExpression::AddressOf(Box::new(object))
                },
            ))
        }
        A::Program(ProgramValue::Pointer(pointer)) if pointer.is_wide() => {
            slices::raise_slice(pointer, parameter_binding, state, bound_variables)
        }
        A::Program(ProgramValue::Pointer(pointer)) => synthesize_surface_pointer_expression(
            pointer,
            parameter_binding,
            state,
            bound_variables,
        ),
        A::Program(ProgramValue::Parameter(term)) => {
            synthesize_surface_algebraic(term, parameter_binding, state, bound_variables)
        }
        A::Algebraic(term) => {
            synthesize_surface_algebraic(term, parameter_binding, state, bound_variables)
        }
        A::Integer(term) => synthesize_surface_integer(
            &term.clone().into(),
            parameter_binding,
            state,
            bound_variables,
        ),
        A::Program(
            ProgramValue::Int8(value)
            | ProgramValue::UInt8(value)
            | ProgramValue::Int16(value)
            | ProgramValue::UInt16(value)
            | ProgramValue::Int32(value)
            | ProgramValue::UInt32(value)
            | ProgramValue::Int64(value)
            | ProgramValue::UInt64(value),
        ) => synthesize_surface_bitvector(value, parameter_binding, state, bound_variables),
        _ => None,
    }
}

/// A call result already carries its native pointer type. When that type
/// supplies the range stride, use the saved pointer directly.
fn synthesize_saved_result_range_base(
    base: &SyntaxTerm,
    range: &MemoryRange,
) -> Option<SyntaxTerm> {
    let SyntaxTerm::RegionResult(region) = base else {
        return None;
    };
    if range.element_width() == 1 && range.carrier_has_known_bounds() {
        return None;
    }
    let selector = ProgramPointSelector::ProgramPoint(ProgramPointRef {
        region: region.clone(),
        kind: ProgramPointKind::Exit,
    });
    SYNTHESIS_RECORDED_POINTS.with(|slot| {
        let points = slot.borrow();
        let points = points.as_ref()?;
        points.get(&selector)?;
        let ProgramValue::Pointer(pointer) = points
            .region_result_value_at(region, Some(&selector))
            .ok()?
        else {
            return None;
        };
        if pointer.address() != range.base()
            || matches!(
                pointer.object_class(),
                Some(crate::kernel::effective_type::CAccessClass::Struct(_))
            )
            || pointer.program_type().pointee_type()?.byte_width() != range.element_width()
        {
            return None;
        }
        Some(SyntaxTerm::At {
            selector,
            expression: Box::new(base.clone()),
        })
    })
}

pub(super) fn synthesize_surface_resource_subject(
    resource: &Resource,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<ResourceSubject> {
    let _frame = SurfaceSynthesisFrame::enter("resource")?;
    if let Resource::Star(pair) = resource {
        return Some(ResourceSubject::Star(
            Box::new(synthesize_surface_resource_subject(
                &pair.0,
                parameter_binding,
                state,
                bound_variables,
            )?),
            Box::new(synthesize_surface_resource_subject(
                &pair.1,
                parameter_binding,
                state,
                bound_variables,
            )?),
        ));
    }
    if matches!(resource, Resource::Emp) {
        return Some(ResourceSubject::Emp);
    }
    // A theorem's resource parameter is its written name, which lowering
    // reads back to the parameter at the same position.
    if let Resource::Parameter(variable) = resource {
        let name = bound_variables.get(variable)?.written()?.to_owned();
        return Some(ResourceSubject::Parameter {
            name,
            index: usize::try_from(variable.0).ok()?,
        });
    }
    // A region's footprint is `R.footprint`, for the region whose recorded
    // entry and exit it runs between; lowering reads that region's footprint
    // back from the same records.
    if let Resource::Footprint(footprint) = resource {
        return SYNTHESIS_RECORDED_POINTS.with(|slot| {
            Some(ResourceSubject::Footprint(
                slot.borrow().as_ref()?.footprint_region(footprint)?,
            ))
        });
    }
    // A declared composite or token is its name applied to its arguments,
    // `list(node)` or `slot(&pool, p)`, which lowering reads back to the
    // same resource.
    if let Resource::Composite { name, arguments } | Resource::Token { name, arguments } = resource
    {
        let kind = if matches!(resource, Resource::Composite { .. }) {
            crate::surface::ResourceKind::Composite
        } else {
            crate::surface::ResourceKind::Token
        };
        let arguments = arguments
            .native_values()
            .iter()
            .map(|argument| {
                synthesize_surface_resource_argument(
                    argument,
                    parameter_binding,
                    state,
                    bound_variables,
                )
            })
            .collect::<Option<Vec<_>>>()?;
        return Some(ResourceSubject::Declared {
            kind,
            name: name.clone(),
            arguments,
            parameter_types: Vec::new(),
        });
    }
    let Resource::Memory(range) = resource else {
        return None;
    };
    // A scalar's storage is its address, not its current value or the zero
    // offset within its block. The slot index supplies the exact local name.
    let surface_base = if let Some(object) = prepared_parameter_object(range.base()) {
        object
    } else if is_materialized_address(range.base()) {
        synthesize_materialized_result(range.base())?
    } else if let Some(name) = state.locals().name_for_slot(range.base()) {
        let object = ProgramExpression::Variable(surface_local_name(name));
        let address = if state.locals().array_object_element_type(name).is_some() {
            object
        } else {
            ProgramExpression::AddressOf(Box::new(object))
        };
        SyntaxTerm::ProgramExpression(address)
    } else {
        synthesize_surface_pointer_expression(
            range.base(),
            parameter_binding,
            state,
            bound_variables,
        )?
    };
    let surface_base =
        if let Some(saved_result) = synthesize_saved_result_range_base(&surface_base, range) {
            saved_result
        } else {
            // A range counts its retained element width, which need not be the
            // pointee width of the name (for example, a struct field's backing).
            // Spell scalar coordinates explicitly; pointer casts retain provenance.
            // An element cast can inherit opaque bounds from its source. Restore
            // root bounds when the range retained them.
            // The whole object of an abstract type, `[p, p + sizeof(T))`, is
            // spelled over its own pointer, which lowers back to that object.
            let abstract_object = range.wide_bounds().is_some_and(|(start, end)| {
                start.uint64_as_const() == Some(0)
                    && crate::kernel::TypeParameterName::of_size_term(end).is_some()
            });
            let surface_base = if matches!(range.element_width(), 1 | 2 | 4 | 8)
                && range.carrier_has_known_bounds()
                && !abstract_object
            {
                synthesize_observation_operand(surface_base, ProgramType::VoidPointer)?
            } else {
                surface_base
            };
            match range.element_width() {
                _ if abstract_object => surface_base,
                1 => synthesize_observation_operand(surface_base, ProgramType::UInt8Pointer)?,
                2 => synthesize_observation_operand(surface_base, ProgramType::UInt16Pointer)?,
                4 => synthesize_observation_operand(surface_base, ProgramType::Int32Pointer)?,
                8 => synthesize_observation_operand(surface_base, ProgramType::UInt64Pointer)?,
                _ => surface_base,
            }
        };
    // A wide range reads its bounds as uint64. A point-named word read
    // carries the bits, so the range supplies the interpretation.
    let wide = range.wide_bounds().is_some();
    let raise_bound = |bound: &OldMachineTerm| {
        if wide
            && matches!(bound, OldMachineTerm::MemoryLoad(point, _, crate::kernel::LoadKind::Bits64)
                if point.read_version_id().is_some())
        {
            return synthesize_typed_word_read(
                bound,
                ProgramType::UInt64,
                parameter_binding,
                state,
                bound_variables,
            );
        }
        synthesize_surface_bitvector(bound, parameter_binding, state, bound_variables)
    };
    let (range_start, range_end) = range.bound_terms();
    let surface_start = raise_bound(range_start)?;
    let surface_end = raise_bound(range_end)?;
    let (Some(semantic_base), Some(start), Some(end)) = (
        contract_expression_to_program_expression(&surface_base),
        contract_expression_to_program_expression(&surface_start),
        contract_expression_to_program_expression(&surface_end),
    ) else {
        return Some(ResourceSubject::SavedMemory {
            base: surface_base,
            start: surface_start,
            end: Some(surface_end),
        });
    };
    Some(ResourceSubject::Memory(ContractSegment {
        uninitialized: false,
        state: ContractSegmentState::Current,
        base: semantic_base,
        start,
        end,
        surface: ContractSegmentSurface::Range {
            base: surface_base,
            start: surface_start,
            end: surface_end,
        },
    }))
}

/// Whether a parameter's bare name still means the value it was passed: false
/// once the function has reassigned it, when the bare name means the new value
/// and the passed one is spelled at function entry instead.
fn parameter_names_its_argument(
    name: &crate::kernel::BindingName,
    argument: &ProgramExpression,
    state: &ExecutionState,
) -> bool {
    let ProgramExpression::Value(passed) = argument else {
        return true;
    };
    state
        .locals()
        .get(name)
        .is_none_or(|current| current.matches_native(passed))
}

pub(super) fn synthesize_surface_pointer_offset(
    term: &AddressOffset,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let _frame = SurfaceSynthesisFrame::enter("pointer-offset")?;
    for (parameter, argument) in parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
    {
        if let ProgramExpression::Value(ProgramValue::Pointer(pointer)) = argument
            && pointer.offset == *term
            && parameter_names_its_argument(
                &crate::surface::surface_parameter_binding(parameter.binding_name()),
                argument,
                state,
            )
        {
            return Some(SyntaxTerm::ProgramExpression(parameter_pointer_name(
                parameter, argument,
            )));
        }
    }
    if let Some(field) = synthesize_parameter_field_pointer_value(term, parameter_binding, state) {
        return Some(field);
    }
    match term.view() {
        OffsetView::Add(left, right) => {
            let indexed_pointer = |base: &AddressOffset, byte_offset: &AddressOffset| {
                let OffsetView::Constant(byte_offset) = byte_offset.view() else {
                    return None;
                };
                if byte_offset % 4 != 0 {
                    return None;
                }
                let SyntaxTerm::ProgramExpression(base) = synthesize_surface_pointer_offset(
                    base,
                    parameter_binding,
                    state,
                    bound_variables,
                )?
                else {
                    return None;
                };
                Some(SyntaxTerm::ProgramExpression(ProgramExpression::Add(
                    Box::new(base),
                    Box::new(ProgramExpression::Value(ProgramValue::Int32(
                        OldMachineTerm::constant((byte_offset / 4) as u32),
                    ))),
                )))
            };
            let dynamically_indexed_pointer = |base: &AddressOffset, index: &AddressOffset| {
                let OffsetView::Int32Scaled {
                    index,
                    byte_width: 4,
                } = index.view()
                else {
                    return None;
                };
                let base =
                    contract_expression_to_program_expression(&synthesize_surface_pointer_offset(
                        base,
                        parameter_binding,
                        state,
                        bound_variables,
                    )?)?;
                let index =
                    contract_expression_to_program_expression(&synthesize_surface_bitvector(
                        index.structural_value(),
                        parameter_binding,
                        state,
                        bound_variables,
                    )?)?;
                Some(SyntaxTerm::ProgramExpression(ProgramExpression::Add(
                    Box::new(base),
                    Box::new(index),
                )))
            };
            indexed_pointer(left, right)
                .or_else(|| indexed_pointer(right, left))
                .or_else(|| dynamically_indexed_pointer(left, right))
                .or_else(|| dynamically_indexed_pointer(right, left))
        }
        OffsetView::Int32Scaled {
            index,
            byte_width: 1 | 4,
        } => synthesize_surface_bitvector(
            index.structural_value(),
            parameter_binding,
            state,
            bound_variables,
        ),
        OffsetView::Constant(_)
        | OffsetView::Variable(_)
        | OffsetView::Int32Scaled { .. }
        | OffsetView::Int64Scaled { .. } => None,
    }
}

/// Names a canonical pointer value through a currently readable pointer field
/// of a struct parameter. Allocation identity conditions compare canonical
/// allocation offsets, not the memory-load syntax that produced them; this
/// reverse lookup recovers stable source syntax at each recorded state.
fn synthesize_parameter_field_pointer_value(
    term: &AddressOffset,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Option<SyntaxTerm> {
    for (parameter, argument) in parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
    {
        let (Some(layout), ProgramExpression::Value(ProgramValue::Pointer(base))) =
            (parameter.struct_layout(), argument)
        else {
            continue;
        };
        for (field_name, field) in layout.fields() {
            let value_type = field.interface_type().to_kernel_type();
            if !value_type.is_pointer() {
                continue;
            }
            let field_pointer = base.offset_by_bytes(field.offset_bytes());
            let loaded_offset = match state.memory().load(&field_pointer) {
                ExpressionOutcome::Value(ProgramValue::Pointer(value)) => value.offset.clone(),
                // Struct pointer fields are represented in contract memory
                // by their pointer-width scalar offset.
                ExpressionOutcome::Value(ProgramValue::Int32(value)) => AddressOffset::scale_int32(
                    value,
                    i64::from(value_type.pointee_type()?.byte_width()),
                ),
                _ => continue,
            };
            if !crate::kernel::offsets_have_same_canonical_form(&loaded_offset, term) {
                continue;
            }
            let base_expression = ProgramExpression::Variable(
                crate::surface::surface_parameter_binding(parameter.binding_name()),
            );
            let lowered_pointer = if field.offset_bytes() == 0 {
                base_expression.clone()
            } else {
                ProgramExpression::PointerOffsetBytes {
                    pointer: Box::new(base_expression.clone()),
                    bytes: field.offset_bytes().into(),
                }
            };
            return Some(SyntaxTerm::Field {
                pointee_struct: None,
                base: Box::new(program_operand(base_expression)),
                field: field_name.clone(),
                lowered: ProgramExpression::TypedLoad {
                    pointer: Box::new(lowered_pointer),
                    value_type,
                    volatile: false,
                    pointee_constant: field.pointee_is_constant(),
                    access_class: None,
                    source: Default::default(),
                },
                offset_bytes: field.offset_bytes().into(),
            });
        }
    }
    // The same lookup through a cast `void *` parameter or a struct-pointer
    // local: a pointer field's cell may hold a view's fresh value rather
    // than a registered load, and this is its only spelling.
    for owner in struct_owners(parameter_binding, state) {
        for (field_name, field) in owner.layout.fields() {
            let value_type = field.interface_type().to_kernel_type();
            if !value_type.is_pointer() {
                continue;
            }
            let field_pointer = owner.pointer.offset_by_bytes(field.offset_bytes());
            let loaded_offset = match state.memory().load(&field_pointer) {
                ExpressionOutcome::Value(ProgramValue::Pointer(value)) => value.offset.clone(),
                ExpressionOutcome::Value(ProgramValue::Int32(value)) => AddressOffset::scale_int32(
                    value,
                    i64::from(value_type.pointee_type()?.byte_width()),
                ),
                _ => continue,
            };
            if !crate::kernel::offsets_have_same_canonical_form(&loaded_offset, term) {
                continue;
            }
            return Some(SyntaxTerm::Field {
                pointee_struct: None,
                base: Box::new(SyntaxTerm::ProgramExpression(owner.base.clone())),
                field: field_name.clone(),
                lowered: ProgramExpression::TypedLoad {
                    pointer: Box::new(owner_field_pointer(&owner.base, field.offset_bytes())),
                    value_type,
                    volatile: false,
                    pointee_constant: field.pointee_is_constant(),
                    access_class: None,
                    source: Default::default(),
                },
                offset_bytes: field.offset_bytes().into(),
            });
        }
    }
    None
}

/// Compatibility entry for pointer carriers still registered under a name.
fn registered_load_in_state(variable: &Variable, state: &ExecutionState) -> Option<OldMachineTerm> {
    let read = crate::kernel::registered_load_term_for_variable(variable)?;
    scalar_read_in_state(&read, state)
}

/// Whether entry/current synthesis is looking at one actual program point.
/// A later point can have equal memory, and two absent IDs prove nothing.
fn synthesis_states_share_program_point(entry: &ExecutionState, state: &ExecutionState) -> bool {
    std::ptr::eq(entry, state)
        || entry
            .program_point()
            .id()
            .is_some_and(|point| state.program_point().id() == Some(point))
}

/// Spell a read whose version is indexed by its program point. A matching
/// current or entry state can name it; otherwise use the version's selector.
fn synthesize_point_read(
    version: &crate::kernel::ProgramPoint,
    pointer: &Address,
    value_type: ProgramType,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    synthesize_spelled_point_read(
        version,
        pointer,
        value_type,
        parameter_binding,
        state,
        bound_variables,
    )
    .map(|(expression, _)| expression)
}

/// Whether a place declared at `declared` names a read decoded at
/// `value_type`. A pointer load nested in an address carries no type of its
/// own (`design/loads.md`, "Raising"): asked at Click's untyped `Pointer`,
/// any pointer declaration names it, object or function, since one cell at
/// one version point is one load whatever type decodes it.
fn place_names_read_at(value_type: ProgramType, declared: ProgramType) -> bool {
    if value_type == ProgramType::Pointer {
        crate::kernel::PointerLoadCategory::of_type(declared).is_some()
    } else {
        declared == value_type
    }
}

/// The type a field or load spelling reads at, from its lowered load.
fn spelled_load_type(expression: &SyntaxTerm) -> Option<ProgramType> {
    match expression {
        SyntaxTerm::Field {
            lowered: ProgramExpression::TypedLoad { value_type, .. },
            ..
        }
        | SyntaxTerm::ProgramExpression(ProgramExpression::TypedLoad { value_type, .. })
        | SyntaxTerm::MemoryLoad { value_type, .. } => Some(*value_type),
        _ => None,
    }
}

/// The pointee type of a pointer place's declaration, when `address` is a
/// bare parameter or local: `*pp` with `int32 **pp` reads an `int32 *`.
/// A local shadows a parameter of the same name, as in C, so the state's
/// locals are asked first.
fn declared_pointee_of_named_pointer(
    address: &SyntaxTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Option<ProgramType> {
    let SyntaxTerm::ProgramExpression(ProgramExpression::Variable(name)) = address else {
        return None;
    };
    let declared = state
        .locals()
        .get(name)
        .map(|local| local.program_type())
        .or_else(|| {
            parameter_binding
                .parameters
                .iter()
                .find(|parameter| {
                    crate::surface::surface_parameter_binding(parameter.binding_name()) == *name
                })
                .map(|parameter| parameter.interface_type().to_kernel_type())
        })?;
    declared
        .pointee_type()
        .filter(|pointee| crate::kernel::PointerLoadCategory::of_type(*pointee).is_some())
}

/// The place that spells the cell at `pointer` read at `value_type` in
/// `state`, with the type it is spelled at: a declared scalar, an owned or
/// declared field, or `load<T>(address)`. Asked at the untyped `Pointer`, a
/// pointer cell is spelled at its declaration's type, or as
/// `load<Pointer>(address)` where no declaration names it.
fn synthesize_cell_place(
    pointer: &Address,
    value_type: ProgramType,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<(SyntaxTerm, ProgramType)> {
    let untyped = value_type == ProgramType::Pointer;
    let spelled = |expression: SyntaxTerm| {
        let ty = spelled_load_type(&expression).unwrap_or(value_type);
        place_names_read_at(value_type, ty).then_some((expression, ty))
    };
    if let Some((name, ty)) = SYNTHESIS_STRUCT_OWNERS.with(|slot| {
        let owners = slot.borrow();
        let (name, ty) = owners.as_ref()?.storage_scalars.get(pointer)?;
        place_names_read_at(value_type, *ty).then(|| (name.clone(), *ty))
    }) {
        return Some((
            SyntaxTerm::ProgramExpression(ProgramExpression::Variable(name)),
            ty,
        ));
    }
    if let Some(field) =
        synthesize_owned_field_at_address(pointer, value_type, state).and_then(&spelled)
    {
        return Some(field);
    }
    let field = if untyped {
        synthesize_parameter_field_load_matching(pointer, None, parameter_binding).or_else(|| {
            synthesize_local_field_load_matching(pointer, None, parameter_binding, state)
        })
    } else {
        synthesize_struct_field_load(pointer, value_type, parameter_binding, state)
    };
    if let Some(field) = field.and_then(&spelled) {
        return Some(field);
    }
    let address =
        synthesize_surface_pointer_expression(pointer, parameter_binding, state, bound_variables)?;
    let load_type = if untyped {
        declared_pointee_of_named_pointer(&address, parameter_binding, state)
            .unwrap_or(ProgramType::Pointer)
    } else {
        value_type
    };
    let address = if value_type == ProgramType::UInt8 {
        synthesize_observation_operand(address, ProgramType::UInt8Pointer)?
    } else {
        address
    };
    Some((synthesize_memory_load(address, load_type), load_type))
}

/// [`synthesize_point_read`], with the type its place spells the read at:
/// `value_type`, or, for a pointer load asked at the untyped `Pointer`, the
/// declared type of the field, slot or parameter that names it. A pointer
/// load no place names spells as `load<Pointer>(address)`.
fn synthesize_spelled_point_read(
    version: &crate::kernel::ProgramPoint,
    pointer: &Address,
    value_type: ProgramType,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<(SyntaxTerm, ProgramType)> {
    let untyped = value_type == ProgramType::Pointer;
    let place = |state: &ExecutionState| {
        synthesize_cell_place(
            pointer,
            value_type,
            parameter_binding,
            state,
            bound_variables,
        )
    };
    // The version the place's own read selects at `state`, read at the type
    // it is spelled at: an untyped nested load is spelled at its place's
    // declared type, object or function pointer, and that read must lower to
    // this load.
    let selects_at = |state: &ExecutionState, ty: ProgramType| {
        state
            .program_point()
            .ordinary_typed_version(pointer, ty)
            .as_ref()
            == Some(version)
    };
    let expression = |state: &ExecutionState| {
        let (expression, ty) = place(state)?;
        if untyped && !version.is_exact_read() && !selects_at(state, ty) {
            return None;
        }
        // The spelling depends on the load's read key, not on which selection
        // built it first: where the place's ordinary read at `state` is this
        // load, it is spelled plainly, and `exact` only where it is not.
        Some((
            if version.is_exact_read() && !selects_at(state, ty) {
                SyntaxTerm::Exact(Box::new(expression))
            } else {
                expression
            },
            ty,
        ))
    };
    let selects_version = |state: &ExecutionState| {
        let point = state.program_point();
        if version.is_exact_read() {
            point.names_exact_read(version)
        } else if untyped {
            // A nested load has no decoding of its own; a version selected
            // for either pointer category may be the one its place names.
            selects_at(state, value_type)
                || selects_at(
                    state,
                    ProgramType::FunctionPointer(crate::kernel::CallbackSignature::UNSPECIFIED),
                )
        } else {
            selects_at(state, value_type)
        }
    };
    if selects_version(state) {
        return expression(state);
    }
    if let Some(entry) = SYNTHESIS_ENTRY_STATE.with(|slot| slot.borrow().clone())
        && selects_version(&entry)
    {
        let (expression, ty) = expression(&entry)?;
        return Some((SyntaxTerm::Old(Box::new(expression)), ty));
    }
    // A checked read of a caller's cell the path leaves unchanged reads it at
    // the function-entry version (`ProgramPoint::entry_integer_version`): it
    // is that cell's entry value, spelled at the entry state.
    if !version.is_exact_read()
        && let Some(kind) = crate::kernel::LoadKind::of_type(value_type)
        && state
            .program_point()
            .entry_integer_version(pointer, kind)
            .as_ref()
            == Some(version)
        && let Some(entry) = SYNTHESIS_ENTRY_STATE.with(|slot| slot.borrow().clone())
    {
        let (expression, ty) = place(&entry)?;
        return Some((SyntaxTerm::Old(Box::new(expression)), ty));
    }
    SYNTHESIS_RECORDED_POINTS.with(|slot| {
        use crate::surface::proof::raise_lower_audit::note_reason;
        let points = slot.borrow();
        let points = points.as_ref()?;
        let Some(selector) = points.point_name(version.read_version_id()?) else {
            note_reason(|| "point read: its version point has no name".to_string());
            return None;
        };
        let Some(recorded) = points.get_exact(selector) else {
            note_reason(|| "point read: its named point has no recorded state".to_string());
            return None;
        };
        if !selects_version(recorded) {
            note_reason(|| {
                "point read: the recorded state at its point selects another version".to_string()
            });
            return None;
        }
        let Some((expression, ty)) = expression(recorded) else {
            note_reason(|| "point read: no place spells its cell at its point".to_string());
            return None;
        };
        Some((
            SyntaxTerm::At {
                selector: selector.clone(),
                expression: Box::new(expression),
            },
            ty,
        ))
    })
}

fn scalar_read_in_state(read: &OldMachineTerm, state: &ExecutionState) -> Option<OldMachineTerm> {
    let OldMachineTerm::MemoryLoad(_, pointer, kind) = read else {
        return None;
    };
    let site = state.program_point();
    let selected = crate::kernel::canonical_form_of_load_at(&site, pointer.as_ref().clone(), *kind);
    (selected == *read).then(|| {
        OldMachineTerm::read_named(
            crate::kernel::ProgramPoint::read_at(site.shared_memory(), &site),
            pointer.as_ref().clone(),
            *kind,
        )
    })
}

// Unsigned division and remainder use the usual C conversion of both
// operands when either operand is uint32. Keep an explicit state outside
// the cast so reconstruction never silently changes which memory is read.
fn synthesize_uint32_operand(expression: SyntaxTerm) -> Option<SyntaxTerm> {
    synthesize_observation_operand(expression, ProgramType::UInt32)
}

/// `expression` converted to `int32`, inside its program point selector: the
/// signed counterpart of [`synthesize_uint32_operand`].
fn synthesize_int32_operand(expression: SyntaxTerm) -> Option<SyntaxTerm> {
    synthesize_observation_operand(expression, ProgramType::Int32)
}

fn variable_spells_uint64(
    variable: Variable,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> bool {
    let term = OldMachineTerm::Variable(variable);
    if let Some(name) = state.locals().names_holding_integer(&term).next() {
        return state
            .locals()
            .get(name)
            .is_some_and(|value| value.program_type() == ProgramType::UInt64);
    }
    describe_parameter_bitvector(&term, parameter_binding).is_some_and(|name| {
        parameter_binding.parameters.iter().any(|parameter| {
            parameter.name() == name
                && parameter.interface_type().to_kernel_type() == ProgramType::UInt64
        })
    })
}

/// Whether [`synthesize_surface_bitvector`] spells `term` as a `uint32`
/// expression: by the name of a `uint32` local or parameter, or as
/// arithmetic the usual conversions make `uint32` because one operand is.
/// It follows that function's choice of name, so it reads one local or
/// parameter per name in the term.
fn bitvector_spells_uint32(
    term: &OldMachineTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> bool {
    if let OldMachineTerm::Variable(variable) = term
        && bound_variables.contains_key(variable)
    {
        return false;
    }
    if term.as_const().is_some() {
        return false;
    }
    if let Some(name) = state.locals().names_holding_integer(term).next() {
        return state
            .locals()
            .get(name)
            .is_some_and(|value| value.program_type() == ProgramType::UInt32);
    }
    if let Some(name) = describe_parameter_bitvector(term, parameter_binding) {
        return parameter_binding.parameters.iter().any(|parameter| {
            parameter.name() == name && parameter.interface_type() == InterfaceType::UInt32
        });
    }
    let either = |left: &OldMachineTerm, right: &OldMachineTerm| {
        bitvector_spells_uint32(left, parameter_binding, state, bound_variables)
            || bitvector_spells_uint32(right, parameter_binding, state, bound_variables)
    };
    match term {
        binary_term!(Int32, Add, left, right)
        | binary_term!(Int32, Subtract, left, right)
        | binary_term!(Int32, Multiply, left, right)
        | binary_term!(Int32, Divide, left, right)
        | binary_term!(Int32, Remainder, left, right) => either(left, right),
        binary_term!(UInt32, Divide, ..) | binary_term!(UInt32, Remainder, ..) => true,
        // A conversion to `uint32`, spelled `x as uint32`.
        OldMachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            to: MachineIntegerType::UInt32,
            ..
        } => true,
        _ => false,
    }
}

/// A population's count at function entry, which the kernel holds as an
/// opaque symbol, is spelled `old(count(R(anchor, _, ...)))`; one a lock
/// acquired is spelled `at(<the lock's region>.exit, count(...))`. A fact the
/// kernel records about it, such as the bound a consumed member places on
/// it, then has a source spelling and can be cited.
fn synthesize_population_entry_count(
    term: &OldMachineTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Option<SyntaxTerm> {
    let OldMachineTerm::Variable(variable) = term else {
        return None;
    };
    let population = state.population_with_entry_count(*variable)?;
    let Some([crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(anchor))]) =
        (population.arguments()).fixed_values::<1>()
    else {
        return None;
    };
    let anchor = synthesize_surface_pointer_expression(
        anchor.address(),
        parameter_binding,
        state,
        &BTreeMap::new(),
    )?;
    let wildcards = population.population_arity().map_or(0, |arity| arity - 1);
    let arguments = std::iter::once(anchor)
        .chain(std::iter::repeat_n(SyntaxTerm::ResourceWildcard, wildcards))
        .collect();
    let count = SyntaxTerm::ResourceCount(Box::new(ResourceClause::Declared {
        type_schema: None,
        resource_type_arguments: Vec::new(),
        resource_arguments: Vec::new(),
        access: ResourceAccessMode::Own,
        kind: ResourceKind::Token,
        name: population.family().to_string(),
        arguments,
        parameter_types: Vec::new(),
    }));
    // A total a lock acquired is the count once the lock returns, where its
    // control holds the population's authority: the exit of the region the
    // lock started at.
    if let Some(point) = state.population_count_acquired_point(*variable) {
        return SYNTHESIS_RECORDED_POINTS.with(|slot| {
            Some(SyntaxTerm::At {
                selector: slot
                    .borrow()
                    .as_ref()?
                    .acquired_total_point(*variable, point)?,
                expression: Box::new(count),
            })
        });
    }
    Some(SyntaxTerm::Old(Box::new(count)))
}

fn synthesize_call_capture(
    state: &ExecutionState,
    name: &crate::kernel::BindingName,
) -> Option<SyntaxTerm> {
    if !name
        .local_id()
        .is_some_and(crate::kernel::LocalBindingId::is_temporary)
    {
        return None;
    }
    SYNTHESIS_RECORDED_POINTS.with(|slot| {
        let slot = slot.borrow();
        let points = slot.as_ref()?;
        let value = state.locals().get(name)?;
        points
            .call_capture_expression(name, value, None)
            .or_else(|| {
                let selector = points.point_name(state.program_point_id()?)?;
                points.call_capture_expression(name, value, Some(selector))
            })
    })
}

fn synthesize_named_integer_local<'a>(
    state: &ExecutionState,
    mut holders: impl Iterator<Item = &'a crate::kernel::BindingName>,
) -> Option<SyntaxTerm> {
    if let Some(name) = holders
        .next()
        .filter(|name| has_surface_iterator_binding(name))
    {
        if name
            .local_id()
            .is_some_and(crate::kernel::LocalBindingId::is_temporary)
        {
            return synthesize_call_capture(state, name);
        }
        return Some(if crate::surface::is_click_value_name(name) {
            SyntaxTerm::ProgramBinding(name.to_string())
        } else {
            SyntaxTerm::ProgramExpression(ProgramExpression::Variable(surface_local_name(name)))
        });
    }
    None
}

/// A retained word read carries its interpretation. Spell that exact typed
/// load, at the same selected state, instead of a signed load followed by
/// an unsigned cast (which introduces a different observation node).
fn synthesize_typed_word_read(
    read: &OldMachineTerm,
    value_type: ProgramType,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let OldMachineTerm::MemoryLoad(memory, pointer, kind) = read else {
        return None;
    };
    if memory.read_version_id().is_some() {
        return synthesize_point_read(
            memory,
            pointer,
            value_type,
            parameter_binding,
            state,
            bound_variables,
        );
    }
    let read = crate::kernel::canonical_form_of_load_at(memory, pointer.as_ref().clone(), *kind);
    let at_state = |load: &OldMachineTerm, state: &ExecutionState| {
        let OldMachineTerm::MemoryLoad(_, pointer, _) = load else {
            return None;
        };
        let address = synthesize_surface_pointer_expression(
            pointer,
            parameter_binding,
            state,
            bound_variables,
        );
        let Some(address) = address else {
            crate::surface::proof::raise_lower_audit::note_reason(|| {
                let variant = |text: String| {
                    text.split(|c: char| !c.is_alphanumeric())
                        .next()
                        .unwrap_or("")
                        .to_string()
                };
                format!(
                    "cell address unspelled: base {}, offset {}",
                    variant(format!("{:?}", pointer.base)),
                    variant(format!("{:?}", pointer.offset))
                )
            });
            return None;
        };
        Some(synthesize_memory_load(address, value_type))
    };
    if let Some(load) = scalar_read_in_state(&read, state) {
        return at_state(&load, state);
    }
    if let Some(entry) = SYNTHESIS_ENTRY_STATE.with(|slot| slot.borrow().clone())
        && let Some(load) = scalar_read_in_state(&read, &entry)
    {
        return Some(SyntaxTerm::Old(Box::new(at_state(&load, &entry)?)));
    }
    let (selector, recorded, load) = recorded_point_of_load(&read)?;
    Some(SyntaxTerm::At {
        selector,
        expression: Box::new(at_state(&load, &recorded)?),
    })
}

fn synthesize_surface_sequence_element(
    value: &ProgramValue,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    match value {
        ProgramValue::Int32(word) | ProgramValue::UInt64(word) => {
            synthesize_surface_bitvector(word, parameter_binding, state, bound)
        }
        _ => None,
    }
}

fn synthesize_surface_sequence(
    value: &crate::kernel::SequenceTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let _frame = SurfaceSynthesisFrame::enter("sequence")?;
    Some(match value.node.as_ref() {
        crate::kernel::SequenceTermNode::Literal(values) => SyntaxTerm::SequenceLiteral(
            values
                .iter()
                .map(|value| {
                    synthesize_surface_sequence_element(value, parameter_binding, state, bound)
                })
                .collect::<Option<Vec<_>>>()?,
        ),
        crate::kernel::SequenceTermNode::Concat(left, right) => SyntaxTerm::SequenceConcat(
            Box::new(synthesize_surface_sequence(
                left,
                parameter_binding,
                state,
                bound,
            )?),
            Box::new(synthesize_surface_sequence(
                right,
                parameter_binding,
                state,
                bound,
            )?),
        ),
    })
}

fn synthesize_surface_bitvector(
    term: &OldMachineTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let _frame = SurfaceSynthesisFrame::enter("bitvector")?;
    let bitvector_frame = SurfaceBitvectorFrame::enter();
    if bitvector_frame.is_outermost() && bitvector_term_exceeds_depth_limit(term) {
        record_surface_synthesis_exhaustion("bitvector");
        return None;
    }
    if let OldMachineTerm::Variable(variable) = term
        && let Some(name) =
            folds::binder_name(false, *variable).or_else(|| bound_variables.get(variable).cloned())
    {
        return Some(SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
            (name.clone()).into(),
        )));
    }
    if let int32_constant!(_) = term {
        return Some(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
            ProgramValue::Int32(term.clone()),
        )));
    }
    // A `uint32` constant keeps its format, so an operator over it spells
    // and lowers back at `uint32`.
    if let uint32_constant!(_) = term {
        return Some(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
            ProgramValue::UInt32(term.clone()),
        )));
    }
    if let Some(named) =
        synthesize_named_integer_local(state, state.locals().names_holding_integer(term))
    {
        return Some(named);
    }
    // The term is the value a parameter was passed. No local holds it now, or
    // the search above would have named it, so if that parameter is a local
    // of this state it has been reassigned, and its bare name means the new
    // value; the passed value is the parameter read at function entry.
    // Naming it by the bare name printed `n <= n` for the invariant
    // `n <= at(loop.entry, n)` in a loop that counts `n` down, which lowers
    // to a different proposition, and `both` then refused to split a bundle
    // whose text did not match its goal.
    if let Some(name) = describe_parameter_bitvector(term, parameter_binding) {
        let reassigned = state.locals().get(&name).is_some();
        return Some(if reassigned {
            SyntaxTerm::At {
                selector: ProgramPointSelector::ProgramPoint(ProgramPointRef {
                    region: CodeRegionRef::Function,
                    kind: ProgramPointKind::Entry,
                }),
                expression: Box::new(if crate::surface::is_click_value_name(&name) {
                    SyntaxTerm::ProgramBinding(name)
                } else {
                    SyntaxTerm::ProgramExpression(ProgramExpression::Variable((name).into()))
                }),
            }
        } else if crate::surface::is_click_value_name(&name) {
            SyntaxTerm::ProgramBinding(name)
        } else {
            SyntaxTerm::ProgramExpression(ProgramExpression::Variable((name).into()))
        });
    }
    if let OldMachineTerm::Variable(variable) = term
        && let Some(name) = proof_binder_name(*variable)
    {
        return Some(SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
            (name).into(),
        )));
    }
    if let Some(region) = SYNTHESIS_RECORDED_POINTS
        .with(|points| points.borrow().as_ref()?.read_event_naming_scalar(term))
    {
        return Some(SyntaxTerm::RegionResult(region));
    }
    if let Some(result) = state_call_result(
        state,
        |value| matches!(value.numeric_value(), ProgramValue::Bool(held) | crate::kernel::integer_c_value!(held) if held == term),
    ) {
        return Some(result);
    }
    if let Some(region) = SYNTHESIS_RECORDED_POINTS
        .with(|slot| slot.borrow().as_ref()?.call_result_naming_integer(term))
    {
        return Some(SyntaxTerm::RegionResult(region));
    }
    if let Some(field) = synthesize_local_aggregate_field(term, state) {
        return Some(field);
    }
    if let Some(field) = synthesize_local_struct_pointer_field(term, parameter_binding, state) {
        return Some(field);
    }
    if let Some(retained_state) = synthesize_state_local(term) {
        return Some(retained_state);
    }
    if let Some(recorded) = synthesize_recorded_local(term) {
        return Some(recorded);
    }
    if let Some(recorded) = synthesize_recorded_cell_value(term, parameter_binding, bound_variables)
    {
        return Some(recorded);
    }
    if let Some(count) = synthesize_population_entry_count(term, parameter_binding, state) {
        return Some(count);
    }
    let binary = |left: &OldMachineTerm, right: &OldMachineTerm| {
        Some((
            Box::new(synthesize_surface_bitvector(
                left,
                parameter_binding,
                state,
                bound_variables,
            )?),
            Box::new(synthesize_surface_bitvector(
                right,
                parameter_binding,
                state,
                bound_variables,
            )?),
        ))
    };
    match term {
        OldMachineTerm::ThreadHandle(_) => {
            unreachable!("a pthread handle must have a source value name at its introduction")
        }
        // A slice application's count raises as `f(x).len()` with the Surface
        // slice type, never as an integer application of `f`.
        OldMachineTerm::PureApplicationCount(_) => {
            slices::raise_slice_count(term, parameter_binding, state, bound_variables)
        }
        // The 32-bit widening of a narrow value is written as the
        // conversion it is (`c as int32`, `c as uint32`).
        OldMachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            value,
            from: source,
            to: destination,
        } if crate::kernel::is_narrow_widening32(*source, *destination) => {
            let operand =
                synthesize_surface_bitvector(value, parameter_binding, state, bound_variables)?;
            if *destination == MachineIntegerType::UInt32 {
                synthesize_uint32_operand(operand)
            } else {
                synthesize_int32_operand(operand)
            }
        }
        OldMachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            value,
            to: destination,
            ..
        } => {
            let operand =
                synthesize_surface_bitvector(value, parameter_binding, state, bound_variables)?;
            Some(SyntaxTerm::CUnary {
                operand: Box::new(operand),
                lowered: ProgramExpression::Cast {
                    expression: Box::new(ProgramExpression::Value(int32(0))),
                    target_type: destination.program_type(),
                    integer_mode: crate::kernel::IntegerCastMode::CConversion,
                    pointee_struct: None,
                    pointee_struct_size: None,
                    pointee_volatile: false,
                    pointee_constant: false,
                    explicit_qualification: false,
                },
            })
        }
        OldMachineTerm::BoolCast { to, value } => {
            // synthesize_surface_bool uses the uint8 carrier to name an
            // unbound Bool variable. Naming above exhausted that route;
            // do not recurse back into the same unnamed variable.
            if *to == MachineIntegerType::UInt8
                && matches!(value.as_ref(), OldConditionTerm::Variable(variable) if !bound_variables.contains_key(variable))
            {
                return None;
            }
            let operand = crate::kernel::KernelTermImport::default().condition(value);
            let term = crate::kernel::KernelTerm::bool_cast(*to, operand).ok()?;
            raise_kernel_term(&term, parameter_binding, state, bound_variables)
        }

        crate::kernel::native_constant!(format, _) => {
            let value = if *format == MachineIntegerType::Int128 {
                ProgramValue::Int128(term.clone())
            } else if *format == MachineIntegerType::UInt128 {
                ProgramValue::UInt128(term.clone())
            } else {
                return None;
            };
            Some(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                value,
            )))
        }
        bits32_constant!(_) => {
            unreachable!("constants returned above")
        }
        binary_term!(Bits32, Add, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(SyntaxTerm::Add(left, right))
        }
        binary_term!(Bits32, Subtract, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(SyntaxTerm::Subtract(left, right))
        }
        binary_term!(Bits32, Multiply, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(SyntaxTerm::Multiply(left, right))
        }
        binary_term!(Int32, Divide, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(SyntaxTerm::Divide(left, right))
        }
        binary_term!(UInt32, Divide, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(SyntaxTerm::Divide(
                left,
                Box::new(synthesize_uint32_operand(*right)?),
            ))
        }
        binary_term!(Int32, Remainder, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(SyntaxTerm::Remainder(left, right))
        }
        binary_term!(UInt32, Remainder, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(SyntaxTerm::Remainder(
                left,
                Box::new(synthesize_uint32_operand(*right)?),
            ))
        }
        binary_term!(Bits32, ShiftLeft, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(SyntaxTerm::ShiftLeft(left, right))
        }
        binary_term!(Int32, ShiftRight, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(SyntaxTerm::ShiftRight(left, right))
        }
        binary_term!(UInt32, ShiftRight, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(SyntaxTerm::ShiftRight(left, right))
        }
        binary_term!(Bits32, BitwiseAnd, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(SyntaxTerm::BitwiseAnd(left, right))
        }
        binary_term!(Bits32, BitwiseOr, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(SyntaxTerm::BitwiseOr(left, right))
        }
        binary_term!(Bits32, BitwiseXor, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(SyntaxTerm::BitwiseXor(left, right))
        }
        unary_term!(Bits32, BitwiseNot, value) => Some(SyntaxTerm::BitwiseNot(Box::new(
            synthesize_surface_bitvector(value, parameter_binding, state, bound_variables)?,
        ))),
        // Floating-point operation terms are not integer surface fragments;
        // callers that need them retain the original C expression instead.
        OldMachineTerm::Float32Negate(_)
        | OldMachineTerm::Float32Binary { .. }
        | OldMachineTerm::Float64Negate(_)
        | OldMachineTerm::Float64Binary { .. } => None,
        OldMachineTerm::IntegerAddress(pointer, _) => {
            let pointer =
                synthesize_surface_pointer(pointer, parameter_binding, state, bound_variables)?;
            Some(SyntaxTerm::ProgramExpression(ProgramExpression::Cast {
                expression: Box::new(pointer),
                target_type: ProgramType::UInt64,
                integer_mode: crate::kernel::IntegerCastMode::Standard,
                pointee_struct: None,
                pointee_struct_size: None,
                pointee_volatile: false,
                pointee_constant: false,
                explicit_qualification: false,
            }))
        }
        OldMachineTerm::MemoryLoad(memory, kernel_pointer, kind) => {
            // A slice's count raises as `s.len()` of the slice read, never as
            // a typed read of one of the cell's words.
            if *kind == crate::kernel::LoadKind::SliceCount {
                return slices::raise_slice_count(term, parameter_binding, state, bound_variables);
            }
            if memory.read_version_id().is_some() {
                let value_type = load_kind_value_type(*kind)?;
                return synthesize_point_read(
                    memory,
                    kernel_pointer,
                    value_type,
                    parameter_binding,
                    state,
                    bound_variables,
                );
            }
            let read = crate::kernel::canonical_form_of_load_at(
                memory,
                kernel_pointer.as_ref().clone(),
                *kind,
            );
            let old = SYNTHESIS_ENTRY_STATE
                .with(|slot| slot.borrow().clone())
                .and_then(|entry| {
                    if synthesis_states_share_program_point(&entry, state) {
                        return None;
                    }
                    let load = scalar_read_in_state(&read, &entry)?;
                    if scalar_read_in_state(&read, state).is_some() {
                        return None;
                    }
                    Some(SyntaxTerm::Old(Box::new(synthesize_surface_bitvector(
                        &load,
                        parameter_binding,
                        &entry,
                        bound_variables,
                    )?)))
                });
            if old.is_some() {
                return old;
            }
            if scalar_read_in_state(&read, state).is_none() {
                return synthesize_read_at_recorded_point(
                    &read,
                    parameter_binding,
                    bound_variables,
                );
            }
            // Address-only names are valid only after selecting this read's
            // epoch. A qualified object or owned field names current memory
            // unless the entry/recorded route above supplies Old or At.
            if *kind == crate::kernel::LoadKind::Int32
                && let Some(field) =
                    synthesize_owned_field_at_address(kernel_pointer, ProgramType::Int32, state)
            {
                return Some(field);
            }

            if *kind == crate::kernel::LoadKind::Int32
                && let Some(field) = synthesize_owned_pointer_field(kernel_pointer, state)
            {
                return Some(SyntaxTerm::Index(
                    Box::new(field),
                    Box::new(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                        int32(0),
                    ))),
                ));
            }

            if let Some(source) = SYNTHESIS_QUALIFIED_SOURCES.with(|slot| {
                slot.borrow()
                    .as_ref()?
                    .storage
                    .qualified_load_sources
                    .get(kernel_pointer.as_ref())
                    .cloned()
            }) {
                return Some(source);
            }
            // A 64-bit read must not fall back to the legacy int32 `load`.
            // Prefer the actual field type; otherwise retain a typed read at
            // the spelled address. The case-split caller checks the spelling
            // against the selected kernel condition before using it.
            if *kind == crate::kernel::LoadKind::Bits64 {
                for value_type in [ProgramType::Int64, ProgramType::UInt64] {
                    if let Some(field) =
                        synthesize_owned_field_at_address(kernel_pointer, value_type, state)
                            .or_else(|| {
                                synthesize_struct_field_load(
                                    kernel_pointer,
                                    value_type,
                                    parameter_binding,
                                    state,
                                )
                            })
                    {
                        return Some(field);
                    }
                }
                if let Some(indexed) = synthesize_local_indexed_load(
                    kernel_pointer,
                    *kind,
                    parameter_binding,
                    state,
                    bound_variables,
                ) {
                    return Some(indexed);
                }
                let value_type = parameter_binding
                    .parameters
                    .iter()
                    .zip(parameter_binding.arguments)
                    .find_map(|(parameter, argument)| {
                        let ProgramExpression::Value(ProgramValue::Pointer(base)) = argument else {
                            return None;
                        };
                        let element_type =
                            parameter.interface_type().pointee_type()?.to_kernel_type();
                        if !matches!(element_type, ProgramType::Int64 | ProgramType::UInt64) {
                            return None;
                        }
                        kernel_pointer.element_index_from_base_with_width(base, 8)?;
                        Some(element_type)
                    })
                    .unwrap_or(ProgramType::Int64);
                let pointer = synthesize_surface_pointer(
                    kernel_pointer,
                    parameter_binding,
                    state,
                    bound_variables,
                )?;
                return Some(SyntaxTerm::ProgramExpression(
                    ProgramExpression::TypedLoad {
                        pointer: Box::new(pointer),
                        value_type,
                        volatile: false,
                        pointee_constant: false,
                        access_class: None,
                        source: Default::default(),
                    },
                ));
            }
            // Globals and function-static scalars have internal slot names
            // that need not be legal source tokens. Use the declaration's
            // spelling, just as the array-element route below does.
            if let Some(name) = SYNTHESIS_STRUCT_OWNERS.with(|slot| {
                let owners = slot.borrow();
                let (name, ty) = owners.as_ref()?.storage_scalars.get(kernel_pointer)?;
                (crate::kernel::LoadKind::of_type(*ty) == Some(*kind)).then(|| name.clone())
            }) {
                return Some(SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                    name,
                )));
            }
            if let Some(name) = state.locals().name_for_slot(kernel_pointer)
                && state.locals().scalar_object_type(name).is_some_and(|ty| {
                    ty.pointee_type().is_none()
                        && crate::kernel::LoadKind::of_type(ty) == Some(*kind)
                })
            {
                Some(SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                    name.clone(),
                )))
            } else if let Some(field) = synthesize_struct_field_load(
                kernel_pointer,
                ProgramType::Int32,
                parameter_binding,
                state,
            ) {
                Some(field)
            } else if let Some(indexed_field) = synthesize_parameter_field_indexed_int32_load(
                kernel_pointer,
                parameter_binding,
                state,
                bound_variables,
            ) {
                Some(indexed_field)
            } else if let Some(element) = synthesize_static_storage_array_element_load(
                kernel_pointer,
                parameter_binding,
                state,
                bound_variables,
            ) {
                Some(element)
            } else if let Some(indexed_local) = synthesize_local_indexed_load(
                kernel_pointer,
                *kind,
                parameter_binding,
                state,
                bound_variables,
            ) {
                Some(indexed_local)
            } else {
                let value_type = parameter_binding
                    .parameters
                    .iter()
                    .zip(parameter_binding.arguments)
                    .find_map(|(parameter, argument)| {
                        let ProgramExpression::Value(ProgramValue::Pointer(base)) = argument else {
                            return None;
                        };
                        // A slice parameter reads its element type through
                        // its data pointer, `bytes.as_ptr()`.
                        let element_type = match parameter.interface_type() {
                            crate::languages::interface::InterfaceType::Slice(element)
                                if base.is_wide() =>
                            {
                                element.thin_pointer_type().pointee_type()?
                            }
                            interface => interface.pointee_type()?.to_kernel_type(),
                        };
                        kernel_pointer
                            .element_index_from_base_with_width(base, element_type.byte_width())?;
                        Some(element_type)
                    });
                // A read through a pointer a pure function returns is a typed
                // read through that call, at the load's own width.
                if matches!(
                    &kernel_pointer.base,
                    AddressBase::PureFunctionApplication(application)
                        if !application.name().starts_with('$')
                ) {
                    let pointer = synthesize_surface_pointer_expression(
                        kernel_pointer,
                        parameter_binding,
                        state,
                        bound_variables,
                    )?;
                    return Some(synthesize_memory_load(
                        pointer,
                        load_kind_value_type(*kind)?,
                    ));
                }
                let pointer = synthesize_surface_pointer(
                    kernel_pointer,
                    parameter_binding,
                    state,
                    bound_variables,
                );
                // A read through a pointer a call returned, at or displaced
                // from the result, is a typed read through that call's
                // result, when it reads exactly the memory being spelled.
                let Some(pointer) = pointer else {
                    // A caller's argument is not the call's: a call that
                    // returns its argument names an address it did not make.
                    if kernel_pointer.base == AddressBase::ExternalArgument {
                        return None;
                    }
                    let value_type = load_kind_value_type(*kind)?;
                    // The read's memory selects `old(..)`, `at(point, ..)` or
                    // the current state; the call's result names the pointer
                    // in that state.
                    return synthesize_at_read_origin(memory, state, |selected| {
                        Some(synthesize_memory_load(
                            call_result_pointer_expression(
                                kernel_pointer,
                                parameter_binding,
                                selected,
                                bound_variables,
                            )?,
                            value_type,
                        ))
                    });
                };
                // An unsigned byte read is spelled as one whatever the
                // pointer's own element type: through a signed plain `char`
                // pointer it is the byte's one name, not the pointer's read.
                // When no pointee type was recovered, the pointer's spelling
                // must not choose the access width. A word read states its
                // own type, including through byte-addressed struct fields.
                let typed_word = value_type.is_none() && *kind == crate::kernel::LoadKind::Int32;
                // Unless the pointer is known to point at `uint8`, a byte read
                // is spelled through an explicit byte view,
                // `*(&dst[i] as (uint8 *))`: a bare `*` reads the pointer's
                // own element type (`int8` through a plain `char *`), and the
                // printed `*` drops a typed load's type.
                let byte_view = *kind == crate::kernel::LoadKind::UInt8
                    && value_type != Some(ProgramType::UInt8);
                let value_type = if *kind == crate::kernel::LoadKind::UInt8 {
                    Some(ProgramType::UInt8)
                } else if typed_word {
                    Some(ProgramType::Int32)
                } else {
                    value_type
                };
                let load = match value_type {
                    _ if byte_view => ProgramExpression::Load(Box::new(ProgramExpression::Cast {
                        expression: Box::new(pointer.clone()),
                        target_type: ProgramType::UInt8Pointer,
                        integer_mode: crate::kernel::IntegerCastMode::Standard,
                        pointee_struct: None,
                        pointee_struct_size: None,
                        pointee_volatile: false,
                        pointee_constant: false,
                        explicit_qualification: false,
                    })),
                    Some(value_type) if value_type == ProgramType::UInt8 || typed_word => {
                        ProgramExpression::TypedLoad {
                            pointer: Box::new(pointer.clone()),
                            value_type,
                            volatile: false,
                            pointee_constant: false,
                            access_class: None,
                            source: Default::default(),
                        }
                    }
                    _ => ProgramExpression::Load(Box::new(pointer.clone())),
                };
                // `synthesize_surface_pointer` names a program parameter or
                // local, never the contract result, so a pointer named like
                // a Click value is read through `program::name`.
                Some(match program_operand(pointer) {
                    operand @ SyntaxTerm::ProgramBinding(_) => SyntaxTerm::CUnary {
                        operand: Box::new(operand),
                        lowered: load,
                    },
                    _ => SyntaxTerm::ProgramExpression(load),
                })
            }
        }
        // A load variable names one cell of one memory version. It denotes
        // the source load of that cell from any state whose memory
        // lies in the same epoch; the kernel's own naming law decides that,
        // so the spelling lowers back to exactly this variable there.
        OldMachineTerm::Variable(variable) => {
            // A slice's count raises as `s.len()` from the name of its slice,
            // never as a variable of its own.
            if variable.counted_slice().is_some() {
                return slices::raise_slice_count(term, parameter_binding, state, bound_variables);
            }
            // A recorded load already supplies the address to inspect. Avoid
            // searching unrelated locals when ordinary certificates name it.
            if let Some((_, pointer)) = crate::kernel::registered_load_for_variable(variable)
                && let Some(name) =
                    state.local_name_holding_bitvector_variable_at(*variable, &pointer)
            {
                return Some(SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                    name.clone(),
                )));
            }
            // A memory-resident scalar local holding exactly this variable
            // reads as its own name here. Looking for aliases is a bounded
            // smart search; a simple certificate never scans unrelated slots.
            if crate::instrumentation::smart_tactic_active()
                && !STRUCTURAL_GOAL_SYNTHESIS.with(|slot| slot.get())
                && let Some(name) = state.local_name_holding_bitvector_variable(*variable)
            {
                return Some(SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                    name.clone(),
                )));
            }
            if let Some(load) = registered_load_in_state(variable, state) {
                return synthesize_surface_bitvector(
                    &load,
                    parameter_binding,
                    state,
                    bound_variables,
                );
            }
            if let Some(field) = synthesize_scalar_model_field(*variable, state) {
                return Some(field);
            }
            SYNTHESIS_ENTRY_STATE
                .with(|slot| {
                    let slot = slot.borrow();
                    let entry = slot.as_ref()?;
                    let load = registered_load_in_state(variable, entry)?;
                    Some(SyntaxTerm::Old(Box::new(synthesize_surface_bitvector(
                        &load,
                        parameter_binding,
                        entry,
                        bound_variables,
                    )?)))
                })
                .or_else(|| {
                    synthesize_load_at_recorded_point(variable, parameter_binding, bound_variables)
                })
        }
        int64_constant!(value) => Some(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
            ProgramValue::Int64(OldMachineTerm::int64_constant(constant_i64(*value))),
        ))),
        uint64_constant!(value) => Some(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
            ProgramValue::UInt64(OldMachineTerm::uint64_constant(constant_u64(*value))),
        ))),
        cast_term!(Int64From32, value)
        | cast_term!(Int64FromUInt32, value)
        | cast_term!(UInt64From32, value)
        | cast_term!(UInt64FromInt32, value)
        | cast_term!(UInt64FromInt64, value) => {
            let mut operand =
                synthesize_surface_bitvector(value, parameter_binding, state, bound_variables)?;
            // Widening interprets the source word's signedness. Its name
            // alone may have a different type (e.g. zero-extending int32 x
            // after `x as uint32`). Preserve that interpretation explicitly.
            if !matches!(term, cast_term!(UInt64FromInt64, _)) {
                let unsigned_source = matches!(
                    term,
                    cast_term!(Int64FromUInt32, _) | cast_term!(UInt64From32, _)
                );
                if unsigned_source {
                    operand = synthesize_uint32_operand(operand)?;
                } else {
                    operand = synthesize_int32_operand(operand)?;
                }
            }
            Some(SyntaxTerm::CUnary {
                operand: Box::new(operand),
                lowered: ProgramExpression::Cast {
                    expression: Box::new(ProgramExpression::Value(int32(0))),
                    target_type: if matches!(
                        term,
                        cast_term!(Int64From32, _) | cast_term!(Int64FromUInt32, _)
                    ) {
                        ProgramType::Int64
                    } else {
                        ProgramType::UInt64
                    },
                    integer_mode: crate::kernel::IntegerCastMode::CConversion,
                    pointee_struct: None,
                    pointee_struct_size: None,
                    pointee_volatile: false,
                    pointee_constant: false,
                    explicit_qualification: false,
                },
            })
        }
        cast_term!(UInt32From64, value) => Some(SyntaxTerm::CUnary {
            operand: Box::new(synthesize_surface_bitvector(
                value,
                parameter_binding,
                state,
                bound_variables,
            )?),
            lowered: ProgramExpression::Cast {
                expression: Box::new(ProgramExpression::Value(int32(0))),
                target_type: ProgramType::UInt32,
                integer_mode: crate::kernel::IntegerCastMode::Standard,
                pointee_struct: None,
                pointee_struct_size: None,
                pointee_volatile: false,
                pointee_constant: false,
                explicit_qualification: false,
            },
        }),
        OldMachineTerm::Binary {
            op, left, right, ..
        } => {
            let (left, right) = binary(left, right)?;
            Some(match op {
                MachineBinaryOp::Add => SyntaxTerm::Add(left, right),
                MachineBinaryOp::Subtract => SyntaxTerm::Subtract(left, right),
                MachineBinaryOp::Multiply => SyntaxTerm::Multiply(left, right),
                MachineBinaryOp::Divide => SyntaxTerm::Divide(left, right),
                MachineBinaryOp::Remainder => SyntaxTerm::Remainder(left, right),
                MachineBinaryOp::ShiftLeft => SyntaxTerm::ShiftLeft(left, right),
                MachineBinaryOp::ShiftRight => SyntaxTerm::ShiftRight(left, right),
                MachineBinaryOp::BitwiseAnd => SyntaxTerm::BitwiseAnd(left, right),
                MachineBinaryOp::BitwiseOr => SyntaxTerm::BitwiseOr(left, right),
                MachineBinaryOp::BitwiseXor => SyntaxTerm::BitwiseXor(left, right),
            })
        }
        OldMachineTerm::Unary {
            op: crate::kernel::MachineUnaryOp::BitwiseNot,
            operand,
            ..
        } => Some(SyntaxTerm::BitwiseNot(Box::new(
            synthesize_surface_bitvector(operand, parameter_binding, state, bound_variables)?,
        ))),
        OldMachineTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            let arm = |term: &OldMachineTerm| {
                let expression =
                    synthesize_surface_bitvector(term, parameter_binding, state, bound_variables)?;
                if is_signed_variable_arithmetic32(term, &expression) {
                    synthesize_int32_operand(expression)
                } else {
                    Some(expression)
                }
            };
            Some(SyntaxTerm::If {
                condition: Box::new(synthesize_surface_proposition_with_bound_variables(
                    &Proposition::condition_is((**condition).clone(), true),
                    parameter_binding,
                    state,
                    bound_variables,
                )?),
                then_branch: Box::new(arm(then_term)?),
                else_branch: Box::new(arm(else_term)?),
            })
        }
        OldMachineTerm::RangeFold { .. } => {
            folds::raise_machine_fold(term, parameter_binding, state, bound_variables)
        }
        // A size or offset term is the value `sizeof(T)` or `offsetof(L, f)`
        // lowers to, kept whole.
        OldMachineTerm::PureFunctionApplication { name, arguments }
            if crate::kernel::layout_term_spelling(name, arguments.len()).is_some() =>
        {
            Some(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                ProgramValue::UInt64(term.clone()),
            )))
        }
        OldMachineTerm::PureFunctionApplication {
            name,
            arguments: values,
        } => Some(SyntaxTerm::Call {
            name: name.clone(),
            arguments: values
                .iter()
                .map(|value| {
                    synthesize_surface_bitvector(value, parameter_binding, state, bound_variables)
                })
                .collect::<Option<Vec<_>>>()?,
        }),
        OldMachineTerm::ClickFunctionApplication {
            name,
            arguments: values,
        } => synthesize_surface_call(name, values, parameter_binding, state, bound_variables),
        OldMachineTerm::IntegerToMachine { value, destination } => {
            let operand = crate::kernel::KernelTermImport::default().integer(value);
            let term = crate::kernel::KernelTerm::integer_to_machine(*destination, operand).ok()?;
            raise_kernel_term(&term, parameter_binding, state, bound_variables)
        }
        OldMachineTerm::AlgebraicMatch { .. } => {
            matches::raise_machine_match(term, parameter_binding, state, bound_variables)
        }
    }
}

/// Restore explicit calls in invariant-body goals so their defining equations
/// can be opened by ordinary `unfold`. Array states are named only when
/// they are exactly the current or function-entry state; no frame search
/// or memory-content comparison is used to choose the spelling.
#[inline(never)]
fn synthesize_surface_call(
    name: &str,
    values: &[crate::kernel::PureFunctionArgument],
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let _frame = SurfaceSynthesisFrame::enter("function-call")?;
    let mut importer = crate::kernel::KernelTermImport::default();
    let arguments = values
        .iter()
        .map(|value| {
            if !consume_surface_synthesis_work("function-argument") {
                return None;
            }
            raise_call_argument(
                &importer.argument(value),
                parameter_binding,
                state,
                bound_variables,
            )
        })
        .collect::<Option<Vec<_>>>()?;
    Some(SyntaxTerm::Call {
        name: generic_instance_source_name(name).into(),
        arguments,
    })
}

/// Name the originating view when the argument retained a recorded point.
fn synthesize_at_program_point(
    point: &crate::kernel::ProgramPoint,
    state: &ExecutionState,
    raise: impl Fn(&ExecutionState) -> Option<SyntaxTerm>,
) -> Option<SyntaxTerm> {
    let matches = |state: &ExecutionState| state.program_point().names_read_view(point);
    if matches(state) {
        return raise(state);
    }
    if let Some(entry) = SYNTHESIS_ENTRY_STATE.with(|slot| slot.borrow().clone())
        && matches(&entry)
    {
        return Some(SyntaxTerm::Old(Box::new(raise(&entry)?)));
    }
    let (selector, recorded) = SYNTHESIS_RECORDED_POINTS.with(|slot| {
        let slot = slot.borrow();
        let points = slot.as_ref()?;
        let (selector, state) = points.point_naming_read(point)?;
        Some((selector.clone(), state.clone()))
    })?;
    Some(SyntaxTerm::At {
        selector,
        expression: Box::new(raise(&recorded)?),
    })
}

fn synthesize_at_read_origin(
    point: &crate::kernel::ProgramPoint,
    state: &ExecutionState,
    raise: impl Fn(&ExecutionState) -> Option<SyntaxTerm>,
) -> Option<SyntaxTerm> {
    if point.id().is_some() {
        synthesize_at_program_point(point, state, raise)
    } else {
        synthesize_at_memory(point.shared_memory(), state, raise)
    }
}

/// A state-bearing argument selects its memory by identity. An intermediate
/// recorded state is as explicit as `old`; no timeline or frame search is
/// needed to recover that state's source selector.
fn synthesize_at_memory(
    memory: &crate::kernel::SharedMemory,
    state: &ExecutionState,
    raise: impl Fn(&ExecutionState) -> Option<SyntaxTerm>,
) -> Option<SyntaxTerm> {
    if *memory == crate::kernel::intern_memory_ref(state.memory()) {
        return raise(state);
    }
    if let Some(entry) = SYNTHESIS_ENTRY_STATE.with(|slot| slot.borrow().clone())
        && *memory == crate::kernel::intern_memory_ref(entry.memory())
    {
        return Some(SyntaxTerm::Old(Box::new(raise(&entry)?)));
    }
    let (selector, recorded) = SYNTHESIS_RECORDED_POINTS.with(|slot| {
        let slot = slot.borrow();
        let (selector, recorded) = slot.as_ref()?.point_reading_memory(memory)?;
        Some((selector.clone(), recorded.clone()))
    })?;
    Some(SyntaxTerm::At {
        selector,
        expression: Box::new(raise(&recorded)?),
    })
}

fn synthesize_legacy_call_argument(
    value: &crate::kernel::PureFunctionArgument,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    Some(match value {
        // As `raise_call_argument`: a proof name, the literal `0` for null,
        // or else the pointer itself.
        crate::kernel::PureFunctionArgument::Value(value @ ProgramValue::Pointer(pointer)) => {
            if let Some(name) = pointer_names::native_name(value) {
                SyntaxTerm::ProgramExpression(ProgramExpression::Variable(name.into()))
            } else if pointer.address() == &Address::null() {
                SyntaxTerm::IntegerLiteral("0".into())
            } else {
                synthesize_surface_value(value, parameter_binding, state)?
            }
        }
        crate::kernel::PureFunctionArgument::Value(ProgramValue::Bool(word)) => {
            synthesize_surface_bool(
                &OldConditionTerm::truth_of_bool_word(word),
                parameter_binding,
                state,
                bound_variables,
            )?
        }
        crate::kernel::PureFunctionArgument::Value(
            value @ (ProgramValue::Float32(_) | ProgramValue::Float64(_)),
        ) if crate::surface::diagnostics::exact_float_literal_spelling(value).is_some() => {
            SyntaxTerm::ProgramExpression(ProgramExpression::Value(value.clone()))
        }
        // A word argument's term carries its own width; the candidate's
        // round trip confirms the call lowers it at the parameter's type.
        crate::kernel::PureFunctionArgument::Value(
            ProgramValue::Int32(value)
            | ProgramValue::UInt32(value)
            | ProgramValue::Int64(value)
            | ProgramValue::UInt64(value)
            | ProgramValue::Int128(value)
            | ProgramValue::UInt128(value),
        ) => synthesize_surface_bitvector(value, parameter_binding, state, bound_variables)?,
        crate::kernel::PureFunctionArgument::SharedMachine(value)
            if value.ty().format().bits() >= 32 =>
        {
            synthesize_surface_bitvector(value.value(), parameter_binding, state, bound_variables)?
        }
        crate::kernel::PureFunctionArgument::Integer(value) => {
            synthesize_surface_integer(value, parameter_binding, state, bound_variables)?
        }
        crate::kernel::PureFunctionArgument::Algebraic(value) => {
            synthesize_surface_algebraic(value, parameter_binding, state, bound_variables)?
        }
        // A pointer's integer address, `address(p)`, or a tag on it,
        // `address(p) + 1`, is spelled by the integer word it projects to,
        // which lowering computes from the same pointer. A word that was
        // passed in or loaded has an identity no spelling of its value keeps.
        crate::kernel::PureFunctionArgument::Value(
            value @ ProgramValue::PointerInteger(record),
        ) if !record.is_opaque_word() => synthesize_legacy_call_argument(
            &crate::kernel::PureFunctionArgument::Value(value.numeric_value().clone()),
            parameter_binding,
            state,
            bound_variables,
        )?,
        // Pointer arrays are imported into ArrayReference before raising.
        _ => return None,
    })
}

fn synthesize_parameter_field_indexed_int32_load(
    pointer: &Address,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let _frame = SurfaceSynthesisFrame::enter("indexed-field")?;
    let pointer_field_and_index = |base: &AddressOffset,
                                   index: Option<&AddressOffset>|
     -> Option<(SyntaxTerm, SyntaxTerm)> {
        let OffsetView::Int32Scaled {
            index: value,
            byte_width: 4,
        } = base.view()
        else {
            return None;
        };
        // The field's value is its load, or the load variable naming that
        // load at this state.
        let named_load = match value.structural_value() {
            OldMachineTerm::Variable(variable) => registered_load_in_state(variable, state),
            _ => None,
        };
        let OldMachineTerm::MemoryLoad(_, field_pointer, _) =
            named_load.as_ref().unwrap_or(value.structural_value())
        else {
            return None;
        };
        let field = synthesize_struct_field_load(
            field_pointer,
            ProgramType::Int32Pointer,
            parameter_binding,
            state,
        )?;
        let index = match index.map(|index| index.view()) {
            None => SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
            Some(OffsetView::Int32Scaled {
                index,
                byte_width: 4,
            }) => synthesize_surface_bitvector(
                index.structural_value(),
                parameter_binding,
                state,
                bound_variables,
            )?,
            Some(OffsetView::Constant(bytes)) if bytes % 4 == 0 => SyntaxTerm::ProgramExpression(
                ProgramExpression::Value(int32(u32::try_from(bytes / 4).ok()?)),
            ),
            Some(_) => return None,
        };
        Some((field, index))
    };
    let (field, index) = match pointer.offset.view() {
        OffsetView::Int32Scaled { .. } | OffsetView::Int64Scaled { .. } => {
            pointer_field_and_index(&pointer.offset, None)?
        }
        OffsetView::Add(left, right) => pointer_field_and_index(left, Some(right))
            .or_else(|| pointer_field_and_index(right, Some(left)))?,
        OffsetView::Constant(_) | OffsetView::Variable(_) => return None,
    };
    // Preserve array indexing for a declared int32 pointer, including fields
    // reached through automatic struct-pointer locals. Their layout is already
    // indexed by local name in the function's synthesis scope.
    if let SyntaxTerm::Field {
        base, field: name, ..
    } = &field
        && let SyntaxTerm::ProgramExpression(ProgramExpression::Variable(owner)) = base.as_ref()
    {
        let has_scalar_stride = |layout: &crate::languages::interface::RecordLayout| {
            layout.fields().get(name).is_some_and(|declaration| {
                declaration.interface_type().to_kernel_type() == ProgramType::Int32Pointer
                    && declaration.struct_name().is_none()
                    && declaration.union_name().is_none()
            })
        };
        let declared_array = parameter_binding
            .parameters
            .iter()
            .find(|parameter| parameter.matches_binding(owner))
            .and_then(|parameter| parameter.struct_layout())
            .map(has_scalar_stride)
            .unwrap_or_else(|| {
                SYNTHESIS_STRUCT_OWNERS.with(|slot| {
                    let owners = slot.borrow();
                    owners
                        .as_ref()
                        .and_then(|owners| owners.locals.get(owner))
                        .is_some_and(has_scalar_stride)
                })
            });
        if declared_array {
            return Some(SyntaxTerm::Index(Box::new(field), Box::new(index)));
        }
    }
    // The kernel indexed a four-byte scalar. The field's written C type
    // may instead be a pointer to a struct, whose indexing scales by that
    // struct's size. Spell the address through the supported byte view and
    // retain the scalar load's width explicitly.
    let bytes = SyntaxTerm::CUnary {
        lowered: ProgramExpression::Cast {
            expression: Box::new(contract_expression_to_program_expression(&field)?),
            target_type: ProgramType::UInt8Pointer,
            integer_mode: crate::kernel::IntegerCastMode::Standard,
            pointee_struct: None,
            pointee_struct_size: None,
            pointee_volatile: false,
            pointee_constant: false,
            explicit_qualification: false,
        },
        operand: Box::new(field),
    };
    let address = SyntaxTerm::Add(
        Box::new(bytes),
        Box::new(SyntaxTerm::Multiply(
            Box::new(index),
            Box::new(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                int32(4),
            ))),
        )),
    );
    Some(SyntaxTerm::CUnary {
        lowered: ProgramExpression::TypedLoad {
            pointer: Box::new(contract_expression_to_program_expression(&address)?),
            value_type: ProgramType::Int32,
            volatile: false,
            pointee_constant: false,
            access_class: None,
            source: Default::default(),
        },
        operand: Box::new(address),
    })
}

/// A scalar field of a struct-pointer parameter or local whose cell holds
/// `term`, spelled `owner->field`. The layouts come from the installed local
/// layout scope; without one, no local is a candidate.
fn synthesize_local_struct_pointer_field(
    term: &OldMachineTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Option<SyntaxTerm> {
    // An abstract cell variable needs its parameter field as a name.
    // Preserve operation syntax for compound terms: naming an arithmetic
    // expression by the field currently holding it creates rewrite cycles.
    let owners = if matches!(term, OldMachineTerm::Variable(_)) {
        range_struct_owners(parameter_binding, state)
    } else {
        struct_owners(parameter_binding, state)
    };
    for owner in owners {
        for (field_name, field) in owner.layout.fields() {
            let value_type = field.interface_type().to_kernel_type();
            if value_type.is_pointer() || value_type.byte_width() == 0 {
                continue;
            }
            let pointer = owner.pointer.offset_by_bytes(field.offset_bytes());
            let ExpressionOutcome::Value(loaded) = state.memory().load(&pointer) else {
                continue;
            };
            let loaded = match loaded.numeric_value().clone() {
                ProgramValue::PointerInteger(_) => unreachable!("numeric projection"),
                ProgramValue::Int8(value) => value,
                ProgramValue::Bool(value)
                | ProgramValue::Int16(value)
                | ProgramValue::Int32(value)
                | ProgramValue::UInt8(value)
                | ProgramValue::UInt16(value)
                | ProgramValue::UInt32(value)
                | ProgramValue::Int64(value)
                | ProgramValue::UInt64(value)
                | ProgramValue::Int128(value)
                | ProgramValue::UInt128(value) => value,
                ProgramValue::Pointer(_)
                | ProgramValue::Parameter(_)
                | ProgramValue::Void
                | ProgramValue::Float32(_)
                | ProgramValue::Float64(_) => {
                    continue;
                }
            };
            if loaded != *term {
                continue;
            }
            return Some(SyntaxTerm::Field {
                pointee_struct: None,
                base: Box::new(SyntaxTerm::ProgramExpression(owner.base.clone())),
                field: field_name.clone(),
                lowered: ProgramExpression::TypedLoad {
                    pointer: Box::new(owner_field_pointer(&owner.base, field.offset_bytes())),
                    value_type,
                    volatile: false,
                    pointee_constant: field.pointee_is_constant(),
                    access_class: None,
                    source: Default::default(),
                },
                offset_bytes: field.offset_bytes().into(),
            });
        }
    }
    None
}

fn synthesize_local_aggregate_field(
    term: &OldMachineTerm,
    state: &ExecutionState,
) -> Option<SyntaxTerm> {
    state
        .locals()
        .aggregate_object_values()
        .find_map(|(name, layout, slot)| {
            layout.fields().iter().find_map(|field| {
                let (element_type, element_count) = match field.program_type() {
                    ProgramType::Int32 => (ProgramType::Int32, 1),
                    ProgramType::UInt8 => (ProgramType::UInt8, 1),
                    ProgramType::Int32Array(length) => (ProgramType::Int32, length),
                    ProgramType::UInt8Array(length) => (ProgramType::UInt8, length),
                    _ => return None,
                };
                (0..element_count).find_map(|index| {
                    let element_offset = field
                        .offset_bytes()
                        .checked_add(index.checked_mul(element_type.byte_width())?)?;
                    let pointer = if element_offset == 0 {
                        slot.clone()
                    } else {
                        slot.with_offset(crate::kernel::AddressOffset::add(
                            slot.offset.clone(),
                            crate::kernel::AddressOffset::constant(i64::from(element_offset)),
                        ))
                    };
                    let ExpressionOutcome::Value(value) = state.memory().load(&pointer) else {
                        return None;
                    };
                    let value_term = match value.numeric_value().clone() {
                        ProgramValue::PointerInteger(_) => unreachable!("numeric projection"),
                        ProgramValue::Int8(value) => value,
                        ProgramValue::Bool(value)
                        | ProgramValue::Int16(value)
                        | ProgramValue::Int32(value)
                        | ProgramValue::UInt8(value)
                        | ProgramValue::UInt16(value)
                        | ProgramValue::UInt32(value)
                        | ProgramValue::Int64(value)
                        | ProgramValue::UInt64(value)
                        | ProgramValue::Int128(value)
                        | ProgramValue::UInt128(value) => value,
                        ProgramValue::Pointer(_)
                        | ProgramValue::Parameter(_)
                        | ProgramValue::Void
                        | ProgramValue::Float32(_)
                        | ProgramValue::Float64(_) => return None,
                    };
                    if value_term != *term {
                        return None;
                    }
                    let base = ProgramExpression::Variable(surface_local_name(name));
                    let lowered_pointer = if field.offset_bytes() == 0 {
                        base.clone()
                    } else {
                        ProgramExpression::PointerOffsetBytes {
                            pointer: Box::new(base.clone()),
                            bytes: field.offset_bytes().into(),
                        }
                    };
                    let field_expression = SyntaxTerm::Field {
                        pointee_struct: None,
                        base: Box::new(SyntaxTerm::ProgramExpression(base)),
                        field: field.name().to_string(),
                        lowered: ProgramExpression::TypedLoad {
                            pointer: Box::new(lowered_pointer),
                            value_type: field.program_type(),
                            volatile: false,
                            pointee_constant: false,
                            access_class: None,
                            source: Default::default(),
                        },
                        offset_bytes: field.offset_bytes().into(),
                    };
                    if element_count == 1 {
                        Some(field_expression)
                    } else if let Some(shape) = field.array_shape() {
                        // Spell the element with one subscript per declared
                        // dimension, as the parser reads it back.
                        let mut remaining = index;
                        let mut indexes = vec![ProgramExpression::Value(int32(0)); shape.len()];
                        for (slot, dimension) in indexes.iter_mut().zip(shape).rev() {
                            *slot = ProgramExpression::Value(int32(remaining % dimension));
                            remaining /= dimension;
                        }
                        let SyntaxTerm::Field { lowered, .. } = &field_expression else {
                            unreachable!()
                        };
                        let lowered = ProgramExpression::Index(
                            Box::new(lowered.clone()),
                            Box::new(crate::surface::parser::flatten_array_indices(
                                indexes.clone(),
                                shape,
                            )),
                        );
                        Some(SyntaxTerm::ArrayIndex {
                            base: Box::new(field_expression),
                            indexes: indexes
                                .into_iter()
                                .map(SyntaxTerm::ProgramExpression)
                                .collect(),
                            dimensions: shape.to_vec(),
                            lowered,
                        })
                    } else {
                        Some(SyntaxTerm::Index(
                            Box::new(field_expression),
                            Box::new(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                                int32(index),
                            ))),
                        ))
                    }
                })
            })
        })
}

#[cfg(test)]
pub(super) fn bitvector_term_is_load_free(term: &OldMachineTerm) -> bool {
    pointer_indices::load_free(crate::kernel::MachineOperandView::Old(term))
}

fn synthesize_local_indexed_load(
    pointer: &Address,
    kind: crate::kernel::LoadKind,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let _frame = SurfaceSynthesisFrame::enter("local-index")?;
    state.locals().object_values().find_map(|(name, value)| {
        let view = value.pointer()?;
        let base = view.address();
        // `local[index]` is the C spelling only when the local is the base
        // the address was formed from: the address is the local's own offset
        // plus an index. Two unrelated pointers into one symbolic block (a
        // struct-pointer local and an array it points to, both external)
        // also have a numeric difference, but indexing the local by it names
        // a different C expression, one that reads the local as an `int32`
        // array and lowers to a different address term.
        if pointer.base != base.base
            || !(matches!(base.offset.view(), OffsetView::Constant(0))
                || matches!(pointer.offset.view(), OffsetView::Add(left, right)
                    if left == &base.offset || right == &base.offset))
        {
            return None;
        }
        let element_type = view.program_type().pointee_type()?;
        if crate::kernel::LoadKind::of_type(element_type) != Some(kind) {
            return None;
        }
        let element_width = element_type.byte_width();
        let index = synthesis_element_index(pointer, base, element_width)?;
        // This candidate is for ordinary `local[index]` forms. If the
        // derived index itself reads memory, trying to synthesize that load
        // can rediscover another local-relative form with a still larger
        // index indefinitely. More specific field and pointer forms are
        // tried by the surrounding reconstruction logic.
        if !pointer_indices::load_free(index.operand_view()) {
            return None;
        }
        Some(SyntaxTerm::Index(
            Box::new(SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                surface_local_name(name),
            ))),
            Box::new(pointer_indices::raise(
                index.operand_view(),
                parameter_binding,
                state,
                bound_variables,
            )?),
        ))
    })
}

/// A 32-bit element read of a global or static array, spelled by the
/// array's source name with one subscript per declared dimension, as the
/// parser reads it back: the array is found by its slot's block, and its
/// shape from the function's declarations. A multidimensional element needs
/// a constant index to split into subscripts.
fn synthesize_static_storage_array_element_load(
    pointer: &Address,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    if !pointer.base.is_static_storage_block() {
        return None;
    }
    let owners = SYNTHESIS_STRUCT_OWNERS.with(|slot| slot.borrow().clone())?;
    state
        .locals()
        .array_objects_with_slot_in(&pointer.base)
        .into_iter()
        .find_map(|(name, element_type, slot)| {
            crate::instrumentation::record_deterministic_work(1);
            if element_type.byte_width() != 4 || element_type.pointee_type().is_some() {
                return None;
            }
            let (source, shape) = owners.storage_arrays.get(name)?;
            let index = pointer.shared_element_index_from_base_with_width(slot, 4)?;
            let base = ProgramExpression::Variable(source.clone());
            if shape.len() <= 1 {
                if !pointer_indices::load_free(index.operand_view()) {
                    return None;
                }
                return Some(SyntaxTerm::Index(
                    Box::new(SyntaxTerm::ProgramExpression(base)),
                    Box::new(pointer_indices::raise(
                        index.operand_view(),
                        parameter_binding,
                        state,
                        bound_variables,
                    )?),
                ));
            }
            let mut remaining = index.operand_view().word32_constant()?;
            let mut indexes = vec![ProgramExpression::Value(int32(0)); shape.len()];
            for (subscript, dimension) in indexes.iter_mut().zip(shape).rev() {
                *subscript = ProgramExpression::Value(int32(remaining % dimension));
                remaining /= dimension;
            }
            let lowered = ProgramExpression::Index(
                Box::new(base.clone()),
                Box::new(crate::surface::parser::flatten_array_indices(
                    indexes.clone(),
                    shape,
                )),
            );
            Some(SyntaxTerm::ArrayIndex {
                base: Box::new(SyntaxTerm::ProgramExpression(base)),
                indexes: indexes
                    .into_iter()
                    .map(SyntaxTerm::ProgramExpression)
                    .collect(),
                dimensions: shape.clone(),
                lowered,
            })
        })
}

fn synthesize_parameter_field_load(
    pointer: &Address,
    value_type: ProgramType,
    parameter_binding: ParameterBinding<'_>,
) -> Option<SyntaxTerm> {
    synthesize_parameter_field_load_matching(pointer, Some(value_type), parameter_binding)
}

fn synthesize_parameter_field_load_matching(
    pointer: &Address,
    value_type: Option<ProgramType>,
    parameter_binding: ParameterBinding<'_>,
) -> Option<SyntaxTerm> {
    for (parameter, argument) in parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
    {
        let (Some(layout), ProgramExpression::Value(ProgramValue::Pointer(base))) = (
            parameter
                .pointee_struct_layout()
                .or_else(|| parameter.struct_layout()),
            argument,
        ) else {
            continue;
        };
        let Some(element_offset) = pointer
            .element_index_from_base(base)
            .and_then(|offset| offset.as_const())
        else {
            continue;
        };
        let offset_bytes = element_offset.checked_mul(4)?;
        let Some((field_name, field)) = layout
            .fields()
            .iter()
            .find(|(_, field)| field.offset_bytes() == offset_bytes)
        else {
            continue;
        };
        let declared_type = field.interface_type().to_kernel_type();
        if !value_type.map_or_else(|| declared_type.is_pointer(), |ty| ty == declared_type) {
            continue;
        }
        let value_type = declared_type;
        let base = ProgramExpression::Variable(crate::surface::surface_parameter_binding(
            parameter.binding_name(),
        ));
        let field_pointer = if offset_bytes == 0 {
            base.clone()
        } else {
            ProgramExpression::PointerOffsetBytes {
                pointer: Box::new(base.clone()),
                bytes: offset_bytes.into(),
            }
        };
        return Some(SyntaxTerm::Field {
            pointee_struct: None,
            base: Box::new(program_operand(base)),
            field: field_name.clone(),
            lowered: ProgramExpression::TypedLoad {
                pointer: Box::new(field_pointer),
                value_type,
                volatile: false,
                pointee_constant: field.pointee_is_constant(),
                access_class: None,
                source: Default::default(),
            },
            offset_bytes: offset_bytes.into(),
        });
    }
    None
}

/// The field read a struct-pointer local performs at `pointer`, spelled
/// `local->field`, when the installed local layout scope knows the local's
/// struct and this state holds the local's pointer value.
fn synthesize_local_field_load(
    pointer: &Address,
    value_type: ProgramType,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Option<SyntaxTerm> {
    synthesize_local_field_load_matching(pointer, Some(value_type), parameter_binding, state)
}

fn synthesize_local_field_load_matching(
    pointer: &Address,
    value_type: Option<ProgramType>,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Option<SyntaxTerm> {
    for owner in struct_owners(parameter_binding, state) {
        // Compare each field's address with the load's pointer directly: an
        // object reached through an opaque `void *` keeps a byte-scaled
        // offset that element arithmetic over the struct width would miss.
        let Some((field_name, field)) = owner.layout.fields().iter().find(|(_, field)| {
            let field_pointer = owner.pointer.offset_by_bytes(field.offset_bytes());
            field_pointer.base == pointer.base
                && crate::kernel::offsets_have_same_canonical_form(
                    &field_pointer.offset,
                    &pointer.offset,
                )
        }) else {
            continue;
        };
        let declared_type = field.interface_type().to_kernel_type();
        if !value_type.map_or_else(|| declared_type.is_pointer(), |ty| ty == declared_type) {
            continue;
        }
        let value_type = declared_type;
        return Some(SyntaxTerm::Field {
            pointee_struct: None,
            base: Box::new(SyntaxTerm::ProgramExpression(owner.base.clone())),
            field: field_name.clone(),
            lowered: ProgramExpression::TypedLoad {
                pointer: Box::new(owner_field_pointer(&owner.base, field.offset_bytes())),
                value_type,
                volatile: false,
                pointee_constant: field.pointee_is_constant(),
                access_class: None,
                source: Default::default(),
            },
            offset_bytes: field.offset_bytes().into(),
        });
    }
    None
}

/// A field read spelled through a struct-pointer parameter or, failing
/// that, through a struct-pointer local of the function under proof.
fn synthesize_struct_field_load(
    pointer: &Address,
    value_type: ProgramType,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Option<SyntaxTerm> {
    synthesize_parameter_field_load(pointer, value_type, parameter_binding)
        .or_else(|| synthesize_local_field_load(pointer, value_type, parameter_binding, state))
}

/// The call result naming `pointer`, or an address displaced from one: the
/// result a call returned into `state`, or one the proof's recorded points
/// name.
fn call_result_pointer_expression(
    pointer: &Address,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    // A slice result names its data pointer only as `R.as_ptr()`
    // (`slices::slice_data_pointer`).
    if let Some(expression) = state_call_result(
        state,
        |value| matches!(value, ProgramValue::Pointer(held) if held.address() == pointer && !held.is_wide()),
    ) {
        return Some(expression);
    }
    if let Some(expression) = SYNTHESIS_RECORDED_POINTS.with(|points| {
        points
            .borrow()
            .as_ref()?
            .call_result_address_expression(pointer)
    }) {
        return Some(expression);
    }
    if !matches!(
        pointer.offset.view(),
        OffsetView::Int32Scaled { .. } | OffsetView::Int64Scaled { .. }
    ) {
        return None;
    }
    // Keep the call as the base and use the index at its original machine
    // width. An exact lookup suffices for a call that introduced this base.
    let base = pointer.with_offset(AddressOffset::constant(0));
    let (region, width) = SYNTHESIS_RECORDED_POINTS.with(|points| {
        let points = points.borrow();
        let points = points.as_ref()?;
        let region = points.call_result_naming_pointer(&base)?;
        let ProgramValue::Pointer(result) = points.region_result_value(&region).ok()? else {
            return None;
        };
        // A record pointer's stride comes from its layout, not its scalar
        // carrier. This path raises indices over ordinary scalar pointees.
        if matches!(
            result.object_class(),
            Some(crate::kernel::effective_type::CAccessClass::Struct(_))
        ) {
            return None;
        }
        Some((region, result.program_type().pointee_type()?.byte_width()))
    })?;
    let index = synthesis_element_index(pointer, &base, width)?;
    Some(SyntaxTerm::Add(
        Box::new(SyntaxTerm::RegionResult(region)),
        Box::new(pointer_indices::raise(
            index.operand_view(),
            parameter_binding,
            state,
            bound_variables,
        )?),
    ))
}

/// The program type a load of `kind` reads.
fn load_kind_value_type(kind: crate::kernel::LoadKind) -> Option<ProgramType> {
    Some(match kind {
        crate::kernel::LoadKind::Int8 => ProgramType::Int8,
        crate::kernel::LoadKind::UInt8 => ProgramType::UInt8,
        crate::kernel::LoadKind::Int16 => ProgramType::Int16,
        crate::kernel::LoadKind::UInt16 => ProgramType::UInt16,
        crate::kernel::LoadKind::Int32 => ProgramType::Int32,
        crate::kernel::LoadKind::UInt32 => ProgramType::UInt32,
        crate::kernel::LoadKind::Bits64 => ProgramType::Int64,
        crate::kernel::LoadKind::Int128 => ProgramType::Int128,
        crate::kernel::LoadKind::UInt128 => ProgramType::UInt128,
        _ => return None,
    })
}

fn synthesize_typed_load(pointer: SyntaxTerm, value_type: ProgramType) -> SyntaxTerm {
    match pointer {
        SyntaxTerm::ProgramExpression(pointer) => {
            SyntaxTerm::ProgramExpression(typed_load_expression(pointer, value_type))
        }
        operand => synthesize_memory_load(operand, value_type),
    }
}

// Lower these reads through the selected memory, even when a program
// expression could also be interpreted as a by-value aggregate projection.
fn synthesize_memory_load(operand: SyntaxTerm, value_type: ProgramType) -> SyntaxTerm {
    SyntaxTerm::MemoryLoad {
        pointer: Box::new(operand),
        value_type,
        volatile: false,
        pointee_constant: false,
    }
}

fn typed_load_expression(pointer: ProgramExpression, value_type: ProgramType) -> ProgramExpression {
    ProgramExpression::TypedLoad {
        pointer: Box::new(pointer),
        value_type,
        volatile: false,
        pointee_constant: false,
        access_class: None,
        source: Default::default(),
    }
}

/// Recover source syntax for an opaque pointer value read from an owned
/// aggregate field. Offset-based synthesis cannot name its distinct block.
/// This is a candidate spelling; callers must re-lower it to the exact fact.
fn synthesize_owned_field_at_address(
    address: &Address,
    value_type: ProgramType,
    state: &ExecutionState,
) -> Option<SyntaxTerm> {
    let name: crate::kernel::BindingName = match &address.base {
        AddressBase::AutomaticLocal { binding, .. } => binding.clone().into(),
        AddressBase::Concrete(block) => block.strip_prefix("local:")?.rsplit(':').next()?.into(),
        _ => return None,
    };
    let slot = state.locals().aggregate_object_pointer(&name)?;
    let layout = state.locals().aggregate_layout(&name)?;
    let field = layout.fields().iter().find(|field| {
        place_names_read_at(value_type, field.program_type())
            && slot.offset_by_layout(field.offset()) == *address
    })?;
    // The field's declaration spells the read; for a typed read it is
    // `value_type` itself.
    let value_type = field.program_type();
    if is_materialized_address(address) {
        return Some(synthesize_typed_load(
            synthesize_materialized_result(address)?,
            value_type,
        ));
    }
    let base = ProgramExpression::Variable(surface_local_name(&name));
    Some(SyntaxTerm::Field {
        pointee_struct: None,
        base: Box::new(SyntaxTerm::ProgramExpression(base.clone())),
        field: field.name().to_string(),
        lowered: ProgramExpression::TypedLoad {
            pointer: Box::new(owner_field_pointer(&base, field.offset())),
            value_type,
            volatile: false,
            pointee_constant: false,
            access_class: None,
            source: Default::default(),
        },
        offset_bytes: field.offset(),
    })
}

/// The address of the pointer read that `pointer` is, when `state` names
/// that read: a legacy load variable whose canonical load in `state` is
/// itself, or a loaded pointer at displacement zero that `state`'s canonical
/// read of its defining address reproduces.
fn pointer_read_address_in_state(pointer: &Address, state: &ExecutionState) -> Option<Address> {
    if !matches!(pointer.offset.view(), OffsetView::Constant(0)) {
        return None;
    }
    let memory = crate::kernel::intern_memory_ref(state.memory());
    match &pointer.base {
        AddressBase::Symbolic(variable) => {
            let (_, address) = crate::kernel::registered_load_for_variable(variable)?;
            registered_load_in_state(variable, state).map(|_| address)
        }
        AddressBase::Load(_) => {
            let read = pointer.as_loaded_value()?;
            // A retained read always names its exact defining state,
            // including a post-store read whose canonical value is now known.
            (memory == read.defining_memory
                || Address::canonical_loaded_value(&memory, &read.defining_address) == *pointer)
                .then_some(read.defining_address)
        }
        _ => None,
    }
}

fn synthesize_owned_pointer_field(pointer: &Address, state: &ExecutionState) -> Option<SyntaxTerm> {
    let address = pointer_read_address_in_state(pointer, state)?;
    let name: crate::kernel::BindingName = match &address.base {
        AddressBase::AutomaticLocal { binding, .. } => binding.clone().into(),
        AddressBase::Concrete(block) => block.strip_prefix("local:")?.rsplit(':').next()?.into(),
        _ => return None,
    };
    let slot = state.locals().aggregate_object_pointer(&name)?;
    let layout = state.locals().aggregate_layout(&name)?;
    let field = layout.fields().iter().find(|field| {
        field.program_type().is_pointer() && slot.offset_by_bytes(field.offset_bytes()) == address
    })?;
    if is_materialized_address(&address) {
        return Some(synthesize_typed_load(
            synthesize_materialized_result(&address)?,
            field.program_type(),
        ));
    }
    let base = ProgramExpression::Variable(surface_local_name(&name));
    Some(SyntaxTerm::Field {
        pointee_struct: None,
        base: Box::new(SyntaxTerm::ProgramExpression(base.clone())),
        field: field.name().to_string(),
        lowered: ProgramExpression::TypedLoad {
            pointer: Box::new(owner_field_pointer(&base, field.offset_bytes())),
            value_type: field.program_type(),
            volatile: false,
            pointee_constant: false,
            access_class: None,
            source: Default::default(),
        },
        offset_bytes: field.offset_bytes().into(),
    })
}

/// The element index `pointer` is at from `base`, as the term a source index
/// expression lowers to. A 64-bit index (`bytes[k]` for a `uint64` `k`) is
/// its own 64-bit value: spelled back, it lowers to the same displacement,
/// and every synthesized candidate is re-lowered and compared before use.
fn synthesis_element_index(
    pointer: &Address,
    base: &Address,
    element_width: u32,
) -> Option<pointer_indices::SourceIndex> {
    // Legacy-only offsets already have a native source reader. Retain that
    // result without importing temporary arithmetic. Any shared child selects
    // the shared path, so this compatibility read cannot export a shared DAG.
    let native = |offset: &AddressOffset| {
        !offset.any_scaled_operand(|index| index.shared_operand().is_some())
    };
    if native(&pointer.offset)
        && native(&base.offset)
        && let Some(index) = pointer.element_index_from_base_with_width(base, element_width)
    {
        return Some(pointer_indices::SourceIndex::Native(index));
    }
    if let Some(index) = pointer.shared_element_index_from_base_with_width(base, element_width) {
        return Some(pointer_indices::SourceIndex::Shared(index));
    }
    if pointer.base != base.base {
        return None;
    }
    let displacement = match pointer.offset.view() {
        _ if matches!(base.offset.view(), OffsetView::Constant(0)) => &pointer.offset,
        OffsetView::Add(left, right) if left == &base.offset => right,
        OffsetView::Add(left, right) if right == &base.offset => left,
        _ => return None,
    };
    match displacement.view() {
        OffsetView::Int64Scaled {
            index,
            byte_width,
            unsigned,
        } if byte_width == i64::from(element_width) => Some(pointer_indices::SourceIndex::Shared(
            pointer_indices::source_index(&index, unsigned),
        )),
        _ => None,
    }
}

/// The parameter whose argument is a pointer, naming that pointer's
/// address: the parameter itself, or `s.as_ptr()` when the argument is a
/// slice `s`, whose name is the slice and not its data pointer
/// (`design/rust-slice-values.md`, step 3b).
fn parameter_pointer_name(
    parameter: &crate::languages::interface::ImportedParameter,
    argument: &ProgramExpression,
) -> ProgramExpression {
    let name = ProgramExpression::Variable(crate::surface::surface_parameter_binding(
        parameter.binding_name(),
    ));
    if matches!(argument, ProgramExpression::Value(ProgramValue::Pointer(passed)) if passed.is_wide())
    {
        ProgramExpression::SliceData(Box::new(name))
    } else {
        name
    }
}

fn synthesize_surface_pointer(
    pointer: &Address,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<ProgramExpression> {
    let _pointer_frame =
        SurfacePointerFrame::enter(pointer, parameter_binding, state, bound_variables)?;
    let _frame = SurfaceSynthesisFrame::enter("pointer")?;
    if pointer == &Address::null() {
        return Some(ProgramExpression::Value(int32(0)));
    }
    if is_materialized_address(pointer) {
        return None;
    }
    if matches!(
        pointer.base,
        AddressBase::ContractResult
            | AddressBase::ContractException
            | AddressBase::AggregateReturn { .. }
            | AddressBase::StringLiteral { .. }
            | AddressBase::AutomaticLocal { .. }
            | AddressBase::ReferenceCarrier { .. }
            | AddressBase::StaticObject { .. }
    ) {
        return Some(ProgramExpression::Value(ProgramValue::typed_pointer(
            pointer.clone(),
            ProgramType::UInt8Pointer,
        )));
    }
    // A function's address spells as the function's name.
    if let (AddressBase::Function(function), OffsetView::Constant(0)) =
        (&pointer.base, pointer.offset.view())
    {
        return Some(ProgramExpression::FunctionAddress(function.clone()));
    }
    // A pointer a proof binder names, such as a match arm's payload.
    if let (AddressBase::Symbolic(variable), OffsetView::Constant(0)) =
        (&pointer.base, pointer.offset.view())
        && let Some(name) =
            folds::binder_name(false, *variable).or_else(|| bound_variables.get(variable).cloned())
    {
        return Some(ProgramExpression::Variable((name.clone()).into()));
    }
    // Exact parameter addresses retain their source identity at proof entry.
    // Naming a stored pointer must not enumerate all earlier parameters.
    if let Some((parameter, argument)) = parameter_binding
        .naming
        .and_then(|names| names.pointer_source(pointer))
        && parameter_names_its_argument(
            &crate::surface::surface_parameter_binding(parameter.binding_name()),
            argument,
            state,
        )
    {
        return Some(parameter_pointer_name(parameter, argument));
    }
    if let Some(expression) = parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
        .find_map(|(parameter, argument)| {
            let ProgramExpression::Value(ProgramValue::Pointer(base)) = argument else {
                return None;
            };
            if !parameter_names_its_argument(
                &crate::surface::surface_parameter_binding(parameter.binding_name()),
                argument,
                state,
            ) {
                return None;
            }
            let element_width = parameter
                .interface_type()
                .pointee_type()?
                .to_kernel_type()
                .byte_width();
            let name = parameter_pointer_name(parameter, argument);
            let element_width = match parameter
                .pointee_struct_layout()
                .or_else(|| parameter.struct_layout())
                .map(crate::languages::interface::RecordLayout::size)
            {
                None => element_width,
                Some(crate::kernel::LayoutSize::Bytes(size)) => size,
                // A symbolic struct has no element stride; its pointer is
                // spelled only at its own address.
                Some(crate::kernel::LayoutSize::Of(_)) => {
                    return (pointer
                        .element_index_from_base_with_width(base, 1)?
                        .as_const()
                        == Some(0))
                    .then_some(name);
                }
            };
            let Some(index) = synthesis_element_index(pointer, base, element_width) else {
                let bytes = pointer
                    .element_index_from_base_with_width(base, 1)?
                    .as_const()?;
                return (bytes <= i32::MAX as u32).then(|| ProgramExpression::PointerOffsetBytes {
                    pointer: Box::new(name),
                    bytes: bytes.into(),
                });
            };
            let base = name;
            if pointer_indices::literal(index.operand_view()) == Some(OldMachineTerm::constant(0)) {
                return Some(base);
            }
            let index = contract_expression_to_program_expression(&pointer_indices::raise(
                index.operand_view(),
                parameter_binding,
                state,
                bound_variables,
            )?)?;
            Some(ProgramExpression::Add(Box::new(base), Box::new(index)))
        })
    {
        return Some(expression);
    }
    if let Some(expression) = state
        .locals()
        .pointer_objects_in_block(&pointer.base)
        .find_map(|(name, base)| {
            crate::instrumentation::record_deterministic_work(1);
            if !has_surface_iterator_binding(name) {
                return None;
            }
            // A slice local names pointers into its data through its data
            // pointer, `local.as_ptr() + k`, never as the slice itself
            // (`design/rust-slice-values.md`, step 4b).
            let slice_element = match base.program_type() {
                ProgramType::SlicePointer(element) if base.is_wide() => Some(element),
                _ => None,
            };
            let element_width = match slice_element {
                Some(element) => element.thin_pointer_type().pointee_type()?.byte_width(),
                None => base.program_type().pointee_type()?.byte_width(),
            };
            let size = SYNTHESIS_STRUCT_OWNERS.with(|slot| {
                slot.borrow()
                    .as_ref()
                    .and_then(|owners| owners.locals.get(name))
                    .map(crate::languages::interface::RecordLayout::size)
            });
            let name = ProgramExpression::Variable(surface_local_name(name));
            let name = if slice_element.is_some() {
                ProgramExpression::SliceData(Box::new(name))
            } else {
                name
            };
            let element_width = match size {
                None => element_width,
                Some(crate::kernel::LayoutSize::Bytes(size)) => size,
                // A symbolic struct has no element stride; its pointer is
                // spelled only at its own address.
                Some(crate::kernel::LayoutSize::Of(_)) => {
                    return (pointer
                        .element_index_from_base_with_width(base, 1)?
                        .as_const()
                        == Some(0))
                    .then_some(name);
                }
            };
            let Some(index) = synthesis_element_index(pointer, base, element_width) else {
                let bytes = pointer
                    .element_index_from_base_with_width(base, 1)?
                    .as_const()?;
                return (bytes <= i32::MAX as u32).then(|| ProgramExpression::PointerOffsetBytes {
                    pointer: Box::new(name),
                    bytes: bytes.into(),
                });
            };
            let base = name;
            if pointer_indices::literal(index.operand_view()) == Some(OldMachineTerm::constant(0)) {
                return Some(base);
            }
            let index = contract_expression_to_program_expression(&pointer_indices::raise(
                index.operand_view(),
                parameter_binding,
                state,
                bound_variables,
            )?)?;
            Some(ProgramExpression::Add(Box::new(base), Box::new(index)))
        })
    {
        return Some(expression);
    }
    // Static scalar and aggregate storage has an indexed source slot too.
    // Name a displaced address from that slot, without scanning objects or
    // pretending the aggregate itself is an array pointer.
    if pointer.base.is_static_storage_block()
        && let OffsetView::Constant(bytes) = pointer.offset.view()
        && let Ok(bytes) = u32::try_from(bytes)
        && let Some(name) = state
            .locals()
            .name_for_slot(&pointer.with_offset(AddressOffset::constant(0)))
        && (state.locals().aggregate_layout(name).is_some()
            || state.locals().scalar_object_type(name).is_some())
    {
        let base = ProgramExpression::AddressOf(Box::new(ProgramExpression::Variable(
            surface_local_name(name),
        )));
        return Some(if bytes == 0 {
            base
        } else {
            ProgramExpression::PointerOffsetBytes {
                pointer: Box::new(base),
                bytes: bytes.into(),
            }
        });
    }
    // A pointer into a global or static array, at a constant byte offset
    // from the array's slot: the array's name, displaced by those bytes.
    if pointer.base.is_static_storage_block()
        && let Some(expression) = state
            .locals()
            .array_objects_with_slot_in(&pointer.base)
            .into_iter()
            .find_map(|(name, _, slot)| {
                crate::instrumentation::record_deterministic_work(1);
                let (OffsetView::Constant(at), OffsetView::Constant(start)) =
                    (pointer.offset.view(), slot.offset.view())
                else {
                    return None;
                };
                let bytes = u32::try_from(at.checked_sub(start)?).ok()?;
                let base = ProgramExpression::Variable(surface_local_name(name));
                Some(if bytes == 0 {
                    base
                } else {
                    ProgramExpression::PointerOffsetBytes {
                        pointer: Box::new(base),
                        bytes: bytes.into(),
                    }
                })
            })
    {
        return Some(expression);
    }
    if let (AddressBase::Symbolic(variable), OffsetView::Constant(0)) =
        (&pointer.base, pointer.offset.view())
        && let Some(name) = proof_binder_name(*variable)
    {
        return Some(ProgramExpression::Variable((name).into()));
    }
    if let Some(field) = synthesize_owned_pointer_field(pointer, state) {
        return contract_expression_to_program_expression(&field);
    }
    // A pointer read from a struct field spells as that field.
    if let Some(read) = pointer.as_loaded_value() {
        if let OffsetView::Constant(bytes) = read.displacement.view()
            && bytes != 0
        {
            let base = pointer.with_offset(AddressOffset::constant(0));
            return Some(ProgramExpression::PointerOffsetBytes {
                pointer: Box::new(synthesize_surface_pointer(
                    &base,
                    parameter_binding,
                    state,
                    bound_variables,
                )?),
                bytes: u32::try_from(bytes).ok()?.into(),
            });
        }
        if !matches!(read.displacement.view(), OffsetView::Constant(0)) {
            return None;
        }
        // A field spelling reads this state; historical reads need their
        // recorded selector before entering this C-only source fragment.
        let defining_address = pointer_read_address_in_state(pointer, state)?;
        // A pointer loaded from a static scalar slot has the declared name
        // and type of that very slot, including its original pointee type.
        if let Some(name) = state.locals().name_for_slot(&defining_address)
            && state
                .global_object_type(name)
                .is_some_and(ProgramType::is_object_pointer)
        {
            return Some(ProgramExpression::Variable(name.clone()));
        }
        // A resource retains an address, not its source pointer type. Recover
        // that type from the field declaration instead of assuming int32*;
        // byte pointers must round-trip through their actual field load.
        let field = synthesize_parameter_field_load_matching(
            &read.defining_address,
            None,
            parameter_binding,
        )
        .or_else(|| {
            synthesize_local_field_load_matching(
                &read.defining_address,
                None,
                parameter_binding,
                state,
            )
        })
        .or_else(|| {
            Some(SyntaxTerm::ProgramExpression(
                ProgramExpression::TypedLoad {
                    pointer: Box::new(synthesize_surface_pointer(
                        &read.defining_address,
                        parameter_binding,
                        state,
                        bound_variables,
                    )?),
                    value_type: ProgramType::Pointer,
                    volatile: false,
                    pointee_constant: false,
                    access_class: None,
                    source: Default::default(),
                },
            ))
        })?;
        return contract_expression_to_program_expression(&field);
    }
    if !parameter_binding.arguments.iter().any(|argument| {
        matches!(
            argument,
            ProgramExpression::Value(ProgramValue::Pointer(base)) if base.base == pointer.base
        )
    }) {
        return None;
    }
    // A pointer read from a struct field spells as that field, possibly
    // displaced; the C expression it denotes is the field's lowered load.
    contract_expression_to_program_expression(&synthesize_surface_pointer_offset(
        &pointer.offset,
        parameter_binding,
        state,
        bound_variables,
    )?)
}

/// `<call>.result` for the result of one of the running statement's call
/// steps that `matches`: the state holds only that statement's calls.
fn state_call_result(
    state: &ExecutionState,
    matches: impl Fn(&ProgramValue) -> bool,
) -> Option<SyntaxTerm> {
    let (step, _) = state.step_results.as_ref()?.iter().find(|(_, value)| {
        crate::instrumentation::record_deterministic_work(1);
        matches(&value.native())
    })?;
    crate::surface::diagnostics::step_result_expression(*step)
}

/// A pointer equality already fixes its operands' types. Preserve that type
/// for arithmetic source operands, whose bare C `Add` otherwise carries no
/// type for its named base and can be misprinted as integer arithmetic.
/// Keep this at the value-comparison boundary: resource addresses retain
/// their existing source places and frontend layout information.
fn synthesize_pointer_equality_operand(
    value: &crate::kernel::Pointer,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    if value.is_wide() {
        return slices::raise_slice(value, parameter_binding, state, bound_variables);
    }
    if let Some(name) = pointer_names::native_name(&ProgramValue::Pointer(value.clone())) {
        return Some(SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
            name.into(),
        )));
    }
    // A pointer converted from an integer word is the written conversion,
    // `(word) as (T *)`. The pointer keeps no struct tag, so the conversion
    // names its pointer type.
    if let Some(bits) = value.integer_cast_word() {
        use crate::surface::proof::raise_lower_audit::note_reason;
        // The word is unsigned; spelled from its bare bits, a 64-bit read
        // would default to `int64` and lower with a conversion.
        let root =
            crate::kernel::KernelTermImport::default().machine(MachineIntegerType::UInt64, bits);
        let Some(word) = raise_kernel_term(&root, parameter_binding, state, bound_variables) else {
            note_reason(|| "integer-converted pointer: its word has no spelling".into());
            return None;
        };
        let Some(operand) =
            crate::surface::lowering::contract_expression_as_program_expression(&word)
        else {
            note_reason(|| {
                "integer-converted pointer: its word is not a current C expression".into()
            });
            return None;
        };
        return Some(crate::surface::lowering::contract_c_unary(
            word,
            ProgramExpression::Cast {
                expression: Box::new(operand),
                target_type: value.program_type(),
                integer_mode: crate::kernel::IntegerCastMode::Standard,
                pointee_struct_size: None,
                pointee_struct: None,
                pointee_volatile: false,
                pointee_constant: false,
                explicit_qualification: false,
            },
        ));
    }
    let address_read = value
        .address()
        .as_loaded_value()
        .filter(|read| matches!(read.displacement.view(), OffsetView::Constant(0)));
    // An address can survive a later store while the complete pointer's
    // provenance still names the earlier read. Spell that value at the
    // state that introduced its domain. A memory-named load whose address
    // and provenance agree needs an explicit state only for a historical read.
    let read_source = value.complete_read_source().or_else(|| {
        let read = address_read.as_ref()?;
        (!read.identity.is_point_named()
            && value.provenance() == value.address()
            && read.defining_memory
                != crate::kernel::intern_memory_ref(state.memory()).unchanged_bytes_source())
        .then(|| (read.defining_memory.clone(), read.defining_address.clone()))
    });
    if let Some((source, address)) = read_source {
        let at_state = |state: &ExecutionState| {
            if let Some(field) = synthesize_struct_field_load(
                &address,
                value.program_type(),
                parameter_binding,
                state,
            ) {
                return Some(field);
            }
            let operand = synthesize_surface_pointer_expression(
                &address,
                parameter_binding,
                state,
                bound_variables,
            )?;
            Some(synthesize_memory_load(operand, value.program_type()))
        };
        use crate::surface::proof::raise_lower_audit::note_reason;
        let unspelled = |place: &str| {
            note_reason(|| format!("snapshot pointer load: no place spells its cell at {place}"));
        };
        if crate::kernel::intern_memory_ref(state.memory()).unchanged_bytes_source()
            == source.unchanged_bytes_source()
        {
            let spelled = at_state(state);
            if spelled.is_none() {
                unspelled("the current state");
            }
            return spelled;
        }
        if let Some((reference, selector)) =
            SYNTHESIS_REFERENCE_STATE.with(|slot| slot.borrow().clone())
            && crate::kernel::intern_memory_ref(reference.memory()).unchanged_bytes_source()
                == source.unchanged_bytes_source()
        {
            let Some(expression) = at_state(&reference) else {
                unspelled("the reference state");
                return None;
            };
            return Some(SyntaxTerm::At {
                selector,
                expression: Box::new(expression),
            });
        }
        if let Some(entry) = SYNTHESIS_ENTRY_STATE.with(|slot| slot.borrow().clone())
            && crate::kernel::intern_memory_ref(entry.memory()).unchanged_bytes_source()
                == source.unchanged_bytes_source()
        {
            let Some(expression) = at_state(&entry) else {
                unspelled("function entry");
                return None;
            };
            return Some(SyntaxTerm::Old(Box::new(expression)));
        }
        return SYNTHESIS_RECORDED_POINTS.with(|slot| {
            let slot = slot.borrow();
            let Some((selector, recorded)) = slot.as_ref()?.point_reading_memory(&source) else {
                let site = address_read
                    .as_ref()
                    .is_some_and(|read| read.point.read_site().is_some());
                note_reason(|| {
                    format!(
                        "snapshot pointer load: its memory matches no recorded point (read site: {})",
                        if site { "yes" } else { "no" }
                    )
                });
                return None;
            };
            let Some(expression) = at_state(recorded) else {
                note_reason(|| {
                    "snapshot pointer load: no place spells its cell at its recorded point"
                        .to_string()
                });
                return None;
            };
            Some(SyntaxTerm::At {
                selector: selector.clone(),
                expression: Box::new(expression),
            })
        });
    }
    // A point-named load is one load at every pointer type; the value
    // being raised is this decoding of it, at the type it was decoded at.
    if let Some(read) = address_read
        && read.identity.is_point_named()
    {
        return synthesize_point_read(
            &read.point,
            &read.defining_address,
            value.program_type(),
            parameter_binding,
            state,
            bound_variables,
        );
    }
    synthesize_pointer_equality_address(
        value.address(),
        value.program_type(),
        parameter_binding,
        state,
        bound_variables,
    )
}

fn synthesize_pointer_equality_address(
    pointer: &Address,
    program_type: ProgramType,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let expression =
        synthesize_surface_pointer_expression(pointer, parameter_binding, state, bound_variables)?;
    let mut inner = &expression;
    while let SyntaxTerm::At { expression, .. } | SyntaxTerm::Old(expression) = inner {
        inner = expression;
    }
    if matches!(
        inner,
        SyntaxTerm::ProgramExpression(ProgramExpression::Add(..) | ProgramExpression::Subtract(..))
            | SyntaxTerm::Add(..)
            | SyntaxTerm::Subtract(..)
    ) {
        synthesize_observation_operand(expression, program_type)
    } else {
        Some(expression)
    }
}

fn is_materialized_address(pointer: &Address) -> bool {
    matches!(&pointer.base, AddressBase::AutomaticLocal { binding, .. } if binding.is_temporary())
}

fn synthesize_materialized_result(pointer: &Address) -> Option<SyntaxTerm> {
    SYNTHESIS_RECORDED_POINTS.with(|points| {
        points
            .borrow()
            .as_ref()?
            .produced_address_expression(pointer)
    })
}

/// `byte_offset(expression, bytes)`, inside any program point selector,
/// as the parser builds it.
fn synthesize_byte_offset(expression: SyntaxTerm, bytes: u32) -> Option<SyntaxTerm> {
    Some(match expression {
        SyntaxTerm::At {
            selector,
            expression,
        } => SyntaxTerm::At {
            selector,
            expression: Box::new(synthesize_byte_offset(*expression, bytes)?),
        },
        SyntaxTerm::Old(expression) => {
            SyntaxTerm::Old(Box::new(synthesize_byte_offset(*expression, bytes)?))
        }
        expression => SyntaxTerm::CUnary {
            operand: Box::new(expression),
            lowered: ProgramExpression::PointerOffsetBytes {
                pointer: Box::new(ProgramExpression::Value(int32(0))),
                bytes: bytes.into(),
            },
        },
    })
}

fn synthesize_surface_pointer_expression(
    pointer: &Address,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let raised = synthesize_surface_pointer_expression_routes(
        pointer,
        parameter_binding,
        state,
        bound_variables,
    );
    if raised.is_none() {
        crate::surface::proof::raise_lower_audit::note_reason(|| {
            let variant = |text: String| {
                text.split(|c: char| !c.is_alphanumeric())
                    .next()
                    .unwrap_or("")
                    .to_string()
            };
            format!(
                "pointer unspelled: base {}, offset {}",
                variant(format!("{:?}", pointer.base)),
                variant(format!("{:?}", pointer.offset))
            )
        });
    }
    if raised.is_none()
        && let Some(read) = pointer.as_loaded_value()
    {
        // Audit only: say what kind of loaded pointer no route spelled.
        crate::surface::proof::raise_lower_audit::note_reason(|| {
            SYNTHESIS_RECORDED_POINTS.with(|slot| {
                let slot = slot.borrow();
                let points = slot.as_ref();
                if let Some(id) = read.point.read_version_id() {
                    let named = points.is_some_and(|points| points.point_name(id).is_some());
                    return format!(
                        "pointer load at a point: {}",
                        if named {
                            "its point is named, no route spelled it"
                        } else {
                            "its version point has no name"
                        }
                    );
                }
                let recorded = points.is_some_and(|points| {
                    points
                        .point_reading_load(&read.point, &read.defining_address)
                        .is_some()
                });
                format!(
                    "pointer load at a snapshot: memory matches {} recorded point (read site: {})",
                    if recorded { "a" } else { "no" },
                    if read.point.read_site().is_some() {
                        "yes"
                    } else {
                        "no"
                    }
                )
            })
        });
    }
    raised
}

fn synthesize_surface_pointer_expression_routes(
    pointer: &Address,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let _frame = SurfaceSynthesisFrame::enter("pointer-expression")?;
    // A slice's data pointer is `s.as_ptr()` of the slice that names it.
    if let Some(data) =
        slices::slice_data_pointer(pointer, parameter_binding, state, bound_variables)
    {
        return Some(data);
    }
    // A call's prepared parameter object is `R.parameter(name)`, which
    // lowers to the object's address as an aggregate local does.
    if let Some(object) = prepared_parameter_object(pointer) {
        return Some(object);
    }
    if matches!(pointer.offset.view(), OffsetView::Constant(0))
        && let Some((name, pointer_type)) =
            crate::surface::proof_diagnostics::render::c_library_pointer_name(pointer)
    {
        return Some(SyntaxTerm::QualifiedC {
            name,
            lowered: ProgramExpression::Value(ProgramValue::typed_pointer(
                pointer.clone(),
                pointer_type,
            )),
        });
    }
    if let Some(read) = pointer.as_loaded_value()
        && let Some((base, value_type)) = synthesize_copied_parameter_pointer(&read, state)
    {
        if matches!(read.displacement.view(), OffsetView::Constant(0)) {
            return Some(base);
        }
        let origin = pointer.with_offset(AddressOffset::constant(0));
        let width = value_type.pointee_type()?.byte_width();
        let index = synthesis_element_index(pointer, &origin, width)?;
        let index = pointer_indices::raise(
            index.operand_view(),
            parameter_binding,
            state,
            bound_variables,
        )?;
        return Some(SyntaxTerm::Add(Box::new(base), Box::new(index)));
    }
    // A pointer load nested in an address has no type of its own: it raises
    // through the place that names it (field, static slot, parameter), at
    // that declaration's type, object or function pointer, or as
    // `load<Pointer>(cell)` where none does (`design/loads.md`, "Raising").
    if let Some(read) = pointer.as_loaded_value()
        && read.identity.is_point_named()
    {
        let (base, spelled_type) = synthesize_spelled_point_read(
            &read.point,
            &read.defining_address,
            ProgramType::Pointer,
            parameter_binding,
            state,
            bound_variables,
        )?;
        if matches!(read.displacement.view(), OffsetView::Constant(0)) {
            return Some(base);
        }
        let origin = pointer.with_offset(AddressOffset::constant(0));
        // Element arithmetic at the declaration's pointee width.
        if let Some(width) = spelled_type
            .pointee_type()
            .map(ProgramType::byte_width)
            .filter(|width| *width != 0)
            && let Some(index) = pointer.element_index_from_base_with_width(&origin, width)
        {
            let index =
                synthesize_surface_bitvector(&index, parameter_binding, state, bound_variables)?;
            return Some(SyntaxTerm::Add(Box::new(base), Box::new(index)));
        }
        // The address holds a byte displacement: a constant one is
        // `byte_offset`, and a scaled index steps a pointer of its stride.
        if let OffsetView::Constant(bytes) = read.displacement.view() {
            return synthesize_byte_offset(base, u32::try_from(bytes).ok()?);
        }
        let stride = match read.displacement.view() {
            OffsetView::Int32Scaled { byte_width, .. }
            | OffsetView::Int64Scaled { byte_width, .. } => byte_width,
            _ => return None,
        };
        // `read.displacement` is the pointer's offset from its load base,
        // the same offset `element_index_from_base_with_width` divides by
        // the stride below: the load base is the undisplaced `origin`.
        let stride_type = match stride {
            1 => ProgramType::UInt8Pointer,
            2 => ProgramType::UInt16Pointer,
            4 => ProgramType::UInt32Pointer,
            8 => ProgramType::UInt64Pointer,
            16 => ProgramType::UInt128Pointer,
            _ => return None,
        };
        let index = pointer.element_index_from_base_with_width(&origin, stride as u32)?;
        let index =
            synthesize_surface_bitvector(&index, parameter_binding, state, bound_variables)?;
        let base = synthesize_observation_operand(base, stride_type)?;
        return Some(SyntaxTerm::Add(Box::new(base), Box::new(index)));
    }
    if matches!(
        pointer.offset.view(),
        OffsetView::Int32Scaled { byte_width: 1, .. }
            | OffsetView::Int64Scaled { byte_width: 1, .. }
    ) && let Some(read) = pointer.as_loaded_value()
        && !read.identity.is_point_named()
    {
        // The raw read's address carrier has no pointee type. Its stored
        // displacement is in bytes, so reproduce it with a byte pointer.
        let origin = pointer.with_offset(AddressOffset::constant(0));
        let cell = pointer_read_address_in_state(&origin, state)?;
        let cell = synthesize_surface_pointer_expression(
            &cell,
            parameter_binding,
            state,
            bound_variables,
        )?;
        let base = synthesize_memory_load(cell, ProgramType::UInt8Pointer);
        let index = synthesis_element_index(pointer, &origin, 1)?;
        let index = pointer_indices::raise(
            index.operand_view(),
            parameter_binding,
            state,
            bound_variables,
        )?;
        return Some(SyntaxTerm::Add(Box::new(base), Box::new(index)));
    }
    // A pointer a pure function returns is that call: its base retains the
    // function and the arguments it was applied to. A kernel-internal
    // function (`$...`) has no Surface spelling.
    if let (AddressBase::PureFunctionApplication(application), OffsetView::Constant(0)) =
        (&pointer.base, pointer.offset.view())
        && !application.name().starts_with('$')
    {
        return synthesize_surface_call(
            application.name(),
            application.arguments(),
            parameter_binding,
            state,
            bound_variables,
        );
    }
    if let Some(region) = SYNTHESIS_RECORDED_POINTS
        .with(|points| points.borrow().as_ref()?.read_event_naming_pointer(pointer))
    {
        return Some(SyntaxTerm::RegionResult(region));
    }
    if let Some(expression) = SYNTHESIS_RECORDED_POINTS.with(|points| {
        points
            .borrow()
            .as_ref()?
            .produced_address_expression(pointer)
    }) {
        return Some(expression);
    }
    if let Some(field) = synthesize_owned_pointer_field(pointer, state) {
        return Some(field);
    }
    if let Some((selector, recorded)) = recorded_point_of_pointer_read(pointer, state) {
        let expression = synthesize_surface_pointer_expression(
            pointer,
            parameter_binding,
            &recorded,
            bound_variables,
        )?;
        return Some(SyntaxTerm::At {
            selector,
            expression: Box::new(expression),
        });
    }
    if let Some(pointer) =
        synthesize_surface_pointer(pointer, parameter_binding, state, bound_variables)
    {
        if let ProgramExpression::Variable(name) = &pointer
            && let Some(result) = synthesize_call_capture(state, name)
        {
            return Some(result);
        }
        return Some(SyntaxTerm::ProgramExpression(pointer));
    }
    if let Some(expression) =
        call_result_pointer_expression(pointer, parameter_binding, state, bound_variables)
    {
        return Some(expression);
    }
    if parameter_binding.arguments.iter().any(|argument| {
        matches!(
            argument,
            ProgramExpression::Value(ProgramValue::Pointer(base)) if base.base == pointer.base
        )
    }) && let Some(offset) = synthesize_surface_pointer_offset(
        &pointer.offset,
        parameter_binding,
        state,
        bound_variables,
    ) {
        return Some(offset);
    }
    synthesize_state_pointer_expression(pointer, parameter_binding, bound_variables)
        .or_else(|| {
            synthesize_entry_pointer_expression(pointer, parameter_binding, state, bound_variables)
        })
        .or_else(|| {
            synthesize_recorded_pointer_expression(pointer, parameter_binding, bound_variables)
        })
        .or_else(|| {
            // A pointer a constant number of bytes past one that has a
            // spelling: that spelling, offset in bytes. Last, so no pointer
            // another route spells (a field, an element) changes.
            let OffsetView::Constant(bytes) = pointer.offset.view() else {
                return None;
            };
            let bytes = u32::try_from(bytes).ok().filter(|bytes| *bytes != 0)?;
            let origin = pointer.with_offset(AddressOffset::constant(0));
            let base = synthesize_surface_pointer_expression(
                &origin,
                parameter_binding,
                state,
                bound_variables,
            )?;
            synthesize_byte_offset(base, bytes)
        })
        .or_else(|| {
            // A memory-named load the state reads is the read of its cell
            // there: the cell's place, as a point-named load is spelled.
            // Last, so no load another route spells changes its spelling.
            if pointer.as_loaded_value()?.identity.is_point_named() {
                return None;
            }
            let cell = pointer_read_address_in_state(pointer, state)?;
            let (place, _) = synthesize_cell_place(
                &cell,
                ProgramType::Pointer,
                parameter_binding,
                state,
                bound_variables,
            )?;
            Some(place)
        })
}

/// A pointer read from the call's private parameter object is named by
/// that call and field: the object is the prepared argument the caller
/// passes as that parameter, `R.parameter(name)`. Like a local it is read in
/// the current state; a read in another recorded memory is spelled at the
/// point that holds it.
fn synthesize_copied_parameter_pointer(
    read: &crate::kernel::LoadedPointerView,
    state: &ExecutionState,
) -> Option<(SyntaxTerm, ProgramType)> {
    SYNTHESIS_RECORDED_POINTS.with(|slot| {
        let points = slot.borrow();
        let points = points.as_ref()?;
        let object = read
            .defining_address
            .with_offset(AddressOffset::constant(0));
        let name =
            crate::kernel::BindingName::from(object.base.prepared_argument_binding()?.clone());
        let (region, parameter, layout) = points.prepared_parameter(&name)?;
        let field = layout.fields().iter().find(|field| {
            let field_type = field.program_type();
            field_type.is_pointer()
                && object.offset_by_layout(field.offset()) == read.defining_address
        })?;
        let value_type = field.program_type();
        let term = SyntaxTerm::Field {
            pointee_struct: None,
            base: Box::new(SyntaxTerm::RegionParameter {
                region,
                name: parameter,
            }),
            field: field.name().to_owned(),
            lowered: typed_load_expression(
                owner_field_pointer(&ProgramExpression::Variable(name.clone()), field.offset()),
                value_type,
            ),
            offset_bytes: field.offset(),
        };
        if crate::kernel::interned_storage_of(state.memory())?.read_identity()
            == read.defining_memory.read_identity()
        {
            return Some((term, value_type));
        }
        let (selector, _) = points.point_reading_memory(&read.defining_memory)?;
        Some((
            SyntaxTerm::At {
                selector: selector.clone(),
                expression: Box::new(term),
            },
            value_type,
        ))
    })
}

/// `at(point, e)` for a pointer no nearer state names, at a recorded point
/// where a local held a pointer into its block: the point that introduced
/// the value, found by the block in one index range.
fn synthesize_recorded_pointer_expression(
    pointer: &Address,
    parameter_binding: ParameterBinding<'_>,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let candidates = SYNTHESIS_RECORDED_POINTS.with(|slot| {
        let slot = slot.borrow();
        let points = slot.as_ref()?;
        Some(
            points
                .points_holding_address_base(&pointer.base)
                .map(|(selector, state)| (selector.clone(), state.clone()))
                .collect::<Vec<_>>(),
        )
    })?;
    candidates.into_iter().find_map(|(selector, state)| {
        let expression =
            synthesize_surface_pointer(pointer, parameter_binding, &state, bound_variables)?;
        if let ProgramExpression::Variable(name) = &expression
            && let Some(result) = SYNTHESIS_RECORDED_POINTS.with(|slot| {
                slot.borrow().as_ref()?.call_capture_expression(
                    name,
                    state.locals().get(name)?,
                    Some(&selector),
                )
            })
        {
            return Some(result);
        }
        Some(SyntaxTerm::At {
            selector,
            expression: Box::new(SyntaxTerm::ProgramExpression(expression)),
        })
    })
}

/// `old(e)` for a pointer the entry state names and this state does not.
/// The entry scope is cleared for the inner synthesis, so it never nests.
fn synthesize_entry_pointer_expression(
    pointer: &Address,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let _ = state;
    let entry = SYNTHESIS_ENTRY_STATE.with(|slot| slot.borrow().clone())?;
    let _cleared = SynthesisEntryScope(SYNTHESIS_ENTRY_STATE.with(|slot| slot.replace(None)));
    let expression =
        synthesize_surface_pointer_expression(pointer, parameter_binding, &entry, bound_variables)?;
    Some(SyntaxTerm::Old(Box::new(expression)))
}

/// A pointer value read from a struct field, whose block is the read itself
/// as a loaded pointer to a heap object is, spelled `local->field` where this
/// state, or failing that the state state as `at(<selector>, ..)`,
/// registers that read.
fn synthesize_loaded_pointer_value(
    pointer: &crate::kernel::Pointer,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Option<SyntaxTerm> {
    let at_state = |state: &ExecutionState| {
        let address = pointer_read_address_in_state(pointer.address(), state)?;
        synthesize_struct_field_load(&address, pointer.program_type(), parameter_binding, state)
    };
    at_state(state)
        .or_else(|| {
            let (retained_state, selector) =
                SYNTHESIS_REFERENCE_STATE.with(|slot| slot.borrow().clone())?;
            let expression = at_state(&retained_state)?;
            Some(SyntaxTerm::At {
                selector,
                expression: Box::new(expression),
            })
        })
        .or_else(|| {
            let (selector, recorded) = recorded_point_of_pointer_read(pointer.address(), state)?;
            Some(SyntaxTerm::At {
                selector,
                expression: Box::new(at_state(&recorded)?),
            })
        })
}

/// The recorded point whose memory holds the pointer read `pointer` is,
/// when `state` does not read it. The read is checked there with the
/// kernel's naming law, as [`pointer_read_address_in_state`] decides it.
fn recorded_point_of_pointer_read(
    pointer: &Address,
    state: &ExecutionState,
) -> Option<(ProgramPointSelector, ExecutionState)> {
    if !matches!(pointer.offset.view(), OffsetView::Constant(0)) {
        return None;
    }
    let memory = match &pointer.base {
        AddressBase::Symbolic(variable) => crate::kernel::registered_load_for_variable(variable)?.0,
        AddressBase::Load(_) => pointer.as_loaded_value()?.defining_memory,
        _ => return None,
    };
    use crate::surface::proof::raise_lower_audit::note_reason;
    if pointer_read_address_in_state(pointer, state).is_some() {
        note_reason(|| {
            "pointer load at a snapshot: the current state reads it, no current route spelled it"
                .to_string()
        });
        return None;
    }
    // Read where the memory is recorded.
    SYNTHESIS_RECORDED_POINTS.with(|slot| {
        let slot = slot.borrow();
        let (selector, recorded) = slot.as_ref()?.point_reading_memory(&memory)?;
        if pointer_read_address_in_state(pointer, recorded).is_none() {
            note_reason(|| {
                "pointer load at a snapshot: the recorded point with its memory does not read it"
                    .to_string()
            });
            return None;
        }
        Some((selector.clone(), recorded.clone()))
    })
}

/// The source spelling of a scalar model-field variable: `o.size` where the
/// current state's instance holds it at that field, `at(<selector>, o.size)`
/// where the state state's does, and `old(o.size)` where the entry
/// state's does. One registry lookup and one instance lookup per state.
fn synthesize_scalar_model_field(variable: Variable, state: &ExecutionState) -> Option<SyntaxTerm> {
    let origin = crate::kernel::model_fields::registered_model_field_origin(variable)?;
    let owner = origin.owner_spelling()?;
    let field_at = |state: &ExecutionState| {
        let instance = state.resource_instance_at_path(origin.identity, &[])?;
        matches!(
            instance.fields().get(origin.field_index),
            Some(crate::kernel::ResourceFieldValue::Program(crate::kernel::integer_c_value!(OldMachineTerm::Variable(held)))) if *held == variable
        )
        .then_some(())?;
        // The field's declared C type, as the parser's elaboration records it.
        let crate::kernel::ResourceFieldType::Program(interface_type) =
            instance.schema().fields().get(origin.field_index)?.1
        else {
            return None;
        };
        Some(SyntaxTerm::ResourceField(ResourceFieldAccess {
            owner: owner.to_string(),
            resource_name: instance.name().to_string(),
            identity: origin.identity.into(),
            children: vec![],
            field: origin.field.to_string(),
            field_index: origin.field_index,
            click_type: Some(ClickType::Program(
                crate::surface::generics::interface_type_from_program_type(interface_type),
            )),
        }))
    };
    if let Some(field) = field_at(state) {
        return Some(field);
    }
    if let Some(field) = SYNTHESIS_REFERENCE_STATE.with(|slot| {
        let slot = slot.borrow();
        let (retained_state, selector) = slot.as_ref()?;
        Some(SyntaxTerm::At {
            selector: selector.clone(),
            expression: Box::new(field_at(retained_state)?),
        })
    }) {
        return Some(field);
    }
    if let Some(field) = SYNTHESIS_ENTRY_STATE.with(|slot| {
        let slot = slot.borrow();
        Some(SyntaxTerm::Old(Box::new(field_at(slot.as_ref()?)?)))
    }) {
        return Some(field);
    }
    // The point whose instance first held this field value, in one lookup.
    SYNTHESIS_RECORDED_POINTS.with(|slot| {
        let slot = slot.borrow();
        let (selector, recorded) = slot.as_ref()?.point_holding_field_value(variable)?;
        Some(SyntaxTerm::At {
            selector: selector.clone(),
            expression: Box::new(field_at(recorded)?),
        })
    })
}

/// The `at(<selector>, e)` spelling of a pointer the current state cannot
/// name but the state state can, such as a call's `old(p->kid)` read at
/// that call's entry. The state scope is cleared for the inner synthesis,
/// so the state spelling never nests.
fn synthesize_state_pointer_expression(
    pointer: &Address,
    parameter_binding: ParameterBinding<'_>,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let (retained_state, selector) =
        SYNTHESIS_REFERENCE_STATE.with(|slot| slot.borrow().clone())?;
    let _cleared =
        SynthesisReferenceStateScope(SYNTHESIS_REFERENCE_STATE.with(|slot| slot.replace(None)));
    let expression = synthesize_surface_pointer_expression(
        pointer,
        parameter_binding,
        &retained_state,
        bound_variables,
    )?;
    Some(SyntaxTerm::At {
        selector,
        expression: Box::new(expression),
    })
}

/// A float load states its width with an existing pointer cast. This keeps the
/// spelling exact even when the available address name is a byte pointer.
fn raise_float_read(
    read: &crate::kernel::KernelMemoryRead,
    value_type: ProgramType,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let (point, address) = read.parts();
    if point.read_version_id().is_some() {
        return synthesize_at_program_point(point, state, |state| {
            let place = raise_float_read_place(
                address,
                value_type,
                parameter_binding,
                state,
                bound_variables,
            )?;
            Some(SyntaxTerm::Exact(Box::new(place)))
        });
    }
    let memory = point.shared_memory();
    // Float producers retain the raw state, rather than the integer load's
    // canonical selection. Spelling must reproduce that same producer input.
    let reads_state = |state: &ExecutionState| {
        crate::kernel::intern_memory_ref(state.memory()).arena_id() == memory.arena_id()
    };
    if !reads_state(state) {
        if let Some(entry) = SYNTHESIS_ENTRY_STATE.with(|slot| slot.borrow().clone())
            && reads_state(&entry)
        {
            return Some(SyntaxTerm::Old(Box::new(raise_float_read(
                read,
                value_type,
                parameter_binding,
                &entry,
                bound_variables,
            )?)));
        }
        let (selector, recorded) = SYNTHESIS_RECORDED_POINTS.with(|slot| {
            let slot = slot.borrow();
            let points = slot.as_ref()?;
            let (selector, recorded) = points.point_reading_memory(memory)?;
            reads_state(recorded).then(|| (selector.clone(), recorded.clone()))
        })?;
        return Some(SyntaxTerm::At {
            selector,
            expression: Box::new(raise_float_read(
                read,
                value_type,
                parameter_binding,
                &recorded,
                bound_variables,
            )?),
        });
    }
    raise_float_read_place(
        address,
        value_type,
        parameter_binding,
        state,
        bound_variables,
    )
}

fn raise_float_read_place(
    address: &crate::kernel::SharedAddress,
    value_type: ProgramType,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let pointer = synthesize_surface_pointer(
        address.written().expect("retained read address"),
        parameter_binding,
        state,
        bound_variables,
    )?;
    Some(SyntaxTerm::Index(
        Box::new(SyntaxTerm::ProgramExpression(ProgramExpression::Cast {
            expression: Box::new(ProgramExpression::Cast {
                expression: Box::new(pointer),
                target_type: ProgramType::VoidPointer,
                integer_mode: crate::kernel::IntegerCastMode::Standard,
                pointee_struct: None,
                pointee_struct_size: None,
                pointee_volatile: false,
                pointee_constant: false,
                explicit_qualification: false,
            }),
            target_type: match value_type {
                ProgramType::Float32 => ProgramType::Float32Pointer,
                ProgramType::Float64 => ProgramType::Float64Pointer,
                _ => unreachable!("float read type"),
            },
            integer_mode: crate::kernel::IntegerCastMode::Standard,
            pointee_struct: None,
            pointee_struct_size: None,
            pointee_volatile: false,
            pointee_constant: false,
            explicit_qualification: false,
        })),
        Box::new(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
            int32(0),
        ))),
    ))
}

/// The source spelling of an algebraic value: a held instance's model field
/// as `instance.field`, from the kernel's model-field registry and the
/// instance the state holds under that identity, and a constructor as
/// `Type::Variant(fields)`. Historical fields use their recorded introduction
/// point; a candidate is admitted only after it re-lowers exactly.
fn synthesize_surface_algebraic(
    term: &crate::kernel::AlgebraicTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let _frame = SurfaceSynthesisFrame::enter("algebraic")?;
    if let crate::kernel::AlgebraicTermNode::Variable(variable) = &term.node
        && let Some(name) = folds::scoped_binder_name(folds::BinderCarrier::Algebraic, *variable)
    {
        return Some(name.reference());
    }
    match &term.node {
        crate::kernel::AlgebraicTermNode::If { .. } => {
            let root = crate::kernel::KernelTermImport::default().algebraic(term);
            raise_kernel_term(&root, parameter_binding, state, bound_variables)
        }
        crate::kernel::AlgebraicTermNode::Match { .. } => {
            let matched = crate::kernel::KernelMatch::import_algebraic(
                &mut crate::kernel::KernelTermImport::default(),
                term,
            )?;
            matches::raise_match(&matched, parameter_binding, state, bound_variables)
        }

        crate::kernel::AlgebraicTermNode::Variable(variable)
            if let Some(name) = bound_variables.get(variable) =>
        {
            Some(name.reference())
        }
        crate::kernel::AlgebraicTermNode::PureFunctionApplication { name, arguments } => {
            synthesize_surface_call(name, arguments, parameter_binding, state, bound_variables)
        }
        crate::kernel::AlgebraicTermNode::Variable(variable) => {
            if let Some(name) = proof_binder_name(*variable) {
                return Some(name.reference());
            }
            // A parameter's own algebraic value is spelled by its name.
            if let Some((parameter, _)) = parameter_binding
                .parameters
                .iter()
                .zip(parameter_binding.arguments)
                .find(|(_, argument)| {
                    matches!(argument, ProgramExpression::Value(ProgramValue::Parameter(value))
                        if value.as_ref() == term)
                })
            {
                return Some(program_operand(ProgramExpression::Variable(
                    crate::surface::surface_parameter_binding(parameter.binding_name()),
                )));
            }
            // A value a call returned is spelled by its call.
            if let Some(result) = state_call_result(
                state,
                |value| matches!(value, ProgramValue::Parameter(held) if held.as_ref() == term),
            ) {
                return Some(result);
            }
            if let Some(region) = SYNTHESIS_RECORDED_POINTS
                .with(|slot| slot.borrow().as_ref()?.call_result_naming_algebraic(term))
            {
                return Some(SyntaxTerm::RegionResult(region));
            }
            // A value a local holds, a Rust local of an enum, a `Vec` or a
            // library iterator, is spelled by that local: now, or at the
            // state the goal reads.
            let held_by = |state: &ExecutionState| {
                state
                    .locals()
                    .names_holding_algebraic(term)
                    .first()
                    .map(|name| {
                        SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                            surface_local_name(name),
                        ))
                    })
            };
            if let Some(local) = held_by(state) {
                return Some(local);
            }
            if let Some(local) = SYNTHESIS_REFERENCE_STATE.with(|slot| {
                let slot = slot.borrow();
                let (state, selector) = slot.as_ref()?;
                Some(SyntaxTerm::At {
                    selector: selector.clone(),
                    expression: Box::new(held_by(state)?),
                })
            }) {
                return Some(local);
            }
            let origin = crate::kernel::model_fields::registered_model_field_origin(*variable)?;
            let owner = origin.owner_spelling()?;
            let field_at = |state: &ExecutionState| {
                let instance = state.resource_instance_at_path(origin.identity, &[])?;
                let held = instance.fields().get(origin.field_index)?;
                let exact = match held {
                    crate::kernel::ResourceFieldValue::Algebraic(value) => value == term,
                    crate::kernel::ResourceFieldValue::Program(ProgramValue::Parameter(value)) => {
                        value.as_ref() == term
                    }
                    _ => false,
                };
                exact.then_some(())?;
                Some(SyntaxTerm::ResourceField(ResourceFieldAccess {
                    owner: owner.to_string(),
                    resource_name: instance.name().to_string(),
                    identity: origin.identity.into(),
                    children: vec![],
                    field: origin.field.to_string(),
                    field_index: origin.field_index,
                    click_type: Some(ClickType::Algebraic(surface_algebraic_type(
                        &term.algebraic_type,
                    )?)),
                }))
            };
            if let Some(field) = field_at(state) {
                return Some(field);
            }
            if let Some(field) = SYNTHESIS_ENTRY_STATE.with(|slot| {
                Some(SyntaxTerm::Old(Box::new(field_at(
                    slot.borrow().as_ref()?,
                )?)))
            }) {
                return Some(field);
            }
            SYNTHESIS_RECORDED_POINTS.with(|slot| {
                let points = slot.borrow();
                let (selector, recorded) = points.as_ref()?.point_holding_field_value(*variable)?;
                Some(SyntaxTerm::At {
                    selector: selector.clone(),
                    expression: Box::new(field_at(recorded)?),
                })
            })
        }

        crate::kernel::AlgebraicTermNode::MemoryLoad { point, pointer }
            if point.read_version_id().is_some() =>
        {
            synthesize_point_algebraic_read(
                &term.algebraic_type,
                point,
                pointer,
                parameter_binding,
                state,
                bound_variables,
            )
        }
        // The value a reference parameter refers to is spelled `*r`.
        crate::kernel::AlgebraicTermNode::MemoryLoad { pointer, .. } => parameter_binding
            .parameters
            .iter()
            .zip(parameter_binding.arguments)
            .find(|(_, argument)| {
                matches!(argument, ProgramExpression::Value(ProgramValue::Pointer(value))
                    if value.address() == pointer.as_ref())
            })
            .map(|(parameter, _)| {
                SyntaxTerm::ProgramExpression(ProgramExpression::Load(Box::new(
                    ProgramExpression::Variable(crate::surface::surface_parameter_binding(
                        parameter.binding_name(),
                    )),
                )))
            })
            .or_else(|| synthesize_held_value_local(term, pointer, state))
            .or_else(|| synthesize_recorded_held_value_local(term, pointer)),
        crate::kernel::AlgebraicTermNode::Constructor { .. } => {
            let root = crate::kernel::KernelTermImport::for_exact_field_inputs().algebraic(term);
            raise_kernel_term(&root, parameter_binding, state, bound_variables)
        }
    }
}

/// The Surface application of a kernel datatype at its type arguments.
fn surface_algebraic_type(
    algebraic_type: &crate::kernel::AlgebraicType,
) -> Option<AlgebraicTypeApplication> {
    Some(AlgebraicTypeApplication {
        rigid: algebraic_type.rigid,
        name: algebraic_type.name.clone(),
        arguments: algebraic_type
            .arguments
            .iter()
            .map(super::pure_theorems::click_type_from_algebraic_value_type)
            .collect::<Result<_, _>>()
            .ok()?,
    })
}

/// A call's prepared parameter object, by its address: the call's
/// `R.parameter(name)`, which lowers to the object as a local does.
fn prepared_parameter_object(slot: &Address) -> Option<SyntaxTerm> {
    if !matches!(slot.offset.view(), OffsetView::Constant(0)) {
        return None;
    }
    let binding = slot.base.prepared_argument_binding()?;
    binding.call_parameter()?;
    let name = crate::kernel::BindingName::from(binding.clone());
    SYNTHESIS_RECORDED_POINTS.with(|points| {
        let (region, parameter, _) = points.borrow().as_ref()?.prepared_parameter(&name)?;
        Some(SyntaxTerm::RegionParameter {
            region,
            name: parameter,
        })
    })
}
