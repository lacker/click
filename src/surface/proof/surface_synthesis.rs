use super::*;
use crate::kernel::MachineBinaryOp;
use crate::kernel::binary_node;
use crate::kernel::{CompareRelation, MachineIntegerType, OverflowOperation};
use crate::kernel::{MachineCastSpelling, cast_term};
use crate::kernel::{binary_term, unary_term};
use crate::kernel::{
    bits32_constant, constant_i64, constant_u64, int32_constant, int64_constant, uint32_constant,
    uint64_constant,
};

#[cfg(test)]
mod tests;

mod folds;
mod matches;
mod pointer_indices;
mod pointer_names;

use crate::kernel::program_local_source_name as surface_local_name;

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
    /// A second reference state, named by its own recorded snapshot selector
    /// rather than by `old(...)`. A loop back edge needs this: the iteration
    /// entry is neither the function entry nor the current state, and the
    /// ranking members compare the two ends of one iteration.
    static SYNTHESIS_SNAPSHOT_STATE: std::cell::RefCell<Option<(ExecutionState, SnapshotSelector)>> = const { std::cell::RefCell::new(None) };
    /// The proof's recorded points. A load registered in a memory that
    /// neither the spelled state nor the entry state reads is spelled at the
    /// point whose memory reads it, found by
    /// [`RecordedSnapshots::point_reading_memory`].
    static SYNTHESIS_RECORDED_POINTS: std::cell::RefCell<Option<RecordedSnapshots>> = const { std::cell::RefCell::new(None) };
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
    /// `__click_q` one, so a proof focused on the synthesized goal names it
    /// the way the source did.
    static SYNTHESIS_BINDER_NAMES: std::cell::RefCell<Option<std::sync::Arc<BTreeMap<Variable, String>>>> =
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
    names: &std::sync::Arc<BTreeMap<Variable, String>>,
    synthesize: impl FnOnce() -> T,
) -> T {
    struct Restore(Option<std::sync::Arc<BTreeMap<Variable, String>>>);
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
    locals: BTreeMap<String, crate::languages::interface::RecordLayout>,
    cast_parameters: BTreeMap<String, (String, crate::languages::interface::RecordLayout)>,
    callback_sources: std::sync::Arc<BTreeMap<String, syntax::CExpression>>,
    /// The function's global and static arrays by kernel and source name: the source name and
    /// declared shape an element read is spelled with.
    storage_arrays: BTreeMap<String, (String, Vec<u32>)>,
    storage_scalars: BTreeMap<Pointer, (String, ProgramType)>,
    /// Declaration spellings for kernel identifiers in retained C arguments.
    storage_source_names: BTreeMap<String, ContractExpression>,
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
                let spelling = (array.name().to_string(), array.shape()?.to_vec());
                Some([
                    (array.kernel_name().to_string(), spelling.clone()),
                    (array.name().to_string(), spelling),
                ])
            })
            .flatten()
            .chain(function.static_arrays().values().flat_map(|array| {
                let spelling = (array.name().to_string(), array.shape().to_vec());
                [
                    (array.kernel_name().to_string(), spelling.clone()),
                    (array.name().to_string(), spelling),
                ]
            }))
            .collect();
        let storage_scalars = function
            .globals()
            .values()
            .map(|global| {
                (
                    Memory::global_pointer(global.kernel_name()),
                    (
                        global.name().to_string(),
                        global.interface_type().to_kernel_type(),
                    ),
                )
            })
            .chain(function.static_locals().values().map(|local| {
                (
                    Memory::static_pointer(function.name(), local.kernel_name()),
                    (
                        local.name().to_string(),
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
            .map(|(kernel, source)| {
                (
                    kernel.to_owned(),
                    ContractExpression::ProgramExpression(ProgramExpression::Variable(
                        source.to_owned(),
                    )),
                )
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
        let expression = owners.as_ref()?.callback_sources.get(name)?;
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
    pointer: crate::kernel::PointerValue,
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
                expression: Box::new(ProgramExpression::Variable(parameter.name().to_string())),
                target_type: ProgramType::Int32Pointer,
                integer_mode: crate::kernel::IntegerCastMode::Standard,
                pointee_struct: Some(struct_name.clone()),
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
                base: ProgramExpression::Variable(surface_local_name(name).to_string()),
                pointer: base.clone(),
                layout: layout.clone(),
            });
        }
    }
    found
}

fn owner_field_pointer(base: &ProgramExpression, offset_bytes: u32) -> ProgramExpression {
    if offset_bytes == 0 {
        base.clone()
    } else {
        ProgramExpression::PointerOffsetBytes {
            pointer: Box::new(base.clone()),
            bytes: offset_bytes,
        }
    }
}

/// A range base synthesis can name: a parameter or local by its spelling,
/// or a pointer field read through a struct-pointer parameter or local.
struct NamedRangeBase {
    lowered: ProgramExpression,
    surface: ContractExpression,
    pointer: crate::kernel::PointerValue,
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
                base: ProgramExpression::Variable(parameter.name().to_string()),
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
    base: &Pointer,
    bytes: &MachineTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Option<ClickProposition> {
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
            return Some(ClickProposition::Loadable {
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
            pointee_volatile: false,
            pointee_constant: false,
            explicit_qualification: false,
        };
        let start = ProgramExpression::Value(int32(start));
        let end = ProgramExpression::Value(int32(end));
        return Some(ClickProposition::Loadable {
            segment: ContractSegment {
                uninitialized: false,
                state: ContractSegmentState::Current,
                base: cast.clone(),
                start: start.clone(),
                end: end.clone(),
                surface: ContractSegmentSurface::Range {
                    base: ContractExpression::ProgramExpression(cast),
                    start: ContractExpression::ProgramExpression(start),
                    end: ContractExpression::ProgramExpression(end),
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
                    let Some(pointer) = Pointer::loaded(&value) else {
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
                surface: ContractExpression::Field {
                    pointee_struct: None,
                    base: Box::new(ContractExpression::ProgramExpression(owner.base.clone())),
                    field: field_name.clone(),
                    lowered: lowered.clone(),
                    offset_bytes: field.offset_bytes(),
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
        .map(|(name, pointer, width)| {
            let lowered = ProgramExpression::Variable(name);
            NamedRangeBase {
                surface: ContractExpression::ProgramExpression(lowered.clone()),
                lowered,
                pointer,
                width,
            }
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
) -> Option<ClickProposition> {
    let _entry =
        SynthesisEntryScope(SYNTHESIS_ENTRY_STATE.with(|slot| slot.replace(Some(entry.clone()))));
    synthesize_surface_proposition(proposition, parameter_binding, post)
}

/// [`synthesize_surface_proposition_at_entry_and_post`] with names for
/// bound variables.
pub(in crate::surface) fn synthesize_surface_proposition_at_entry_post_with_bound_variable_names(
    proposition: &Proposition,
    parameter_binding: ParameterBinding<'_>,
    entry: &ExecutionState,
    post: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ClickProposition> {
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
/// snapshot selector. A value the current state no longer holds but the
/// snapshot state does reads as `at(<selector>, name)`, which is the same
/// spelling loop-body premises already use, so the synthesized form lowers
/// back to exactly this term at the snapshot the selector names.
pub(in crate::surface) fn synthesize_surface_proposition_at_entry_post_and_snapshot(
    proposition: &Proposition,
    parameter_binding: ParameterBinding<'_>,
    entry: &ExecutionState,
    post: &ExecutionState,
    snapshot: Option<(&ExecutionState, &SnapshotSelector)>,
) -> Option<ClickProposition> {
    let _snapshot = SynthesisSnapshotScope(SYNTHESIS_SNAPSHOT_STATE.with(|slot| {
        slot.replace(snapshot.map(|(state, selector)| (state.clone(), selector.clone())))
    }));
    synthesize_surface_proposition_at_entry_and_post(proposition, parameter_binding, entry, post)
}

struct SynthesisSnapshotScope(Option<(ExecutionState, SnapshotSelector)>);
impl Drop for SynthesisSnapshotScope {
    fn drop(&mut self) {
        SYNTHESIS_SNAPSHOT_STATE.with(|slot| {
            slot.replace(self.0.take());
        });
    }
}

/// Spells loads registered at the proof's recorded points while alive.
pub(in crate::surface) struct SynthesisRecordedPointsScope(Option<RecordedSnapshots>);

impl SynthesisRecordedPointsScope {
    pub(in crate::surface) fn enter(points: &RecordedSnapshots) -> Self {
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

/// A recorded state whose structural read selection reproduces this read.
/// Prefer the point recording its memory, then indexed nearby points.
fn recorded_point_of_load(
    read: &MachineTerm,
) -> Option<(SnapshotSelector, ExecutionState, MachineTerm)> {
    let MachineTerm::MemoryLoad(memory, _, _) = read else {
        return None;
    };
    SYNTHESIS_RECORDED_POINTS.with(|slot| {
        let slot = slot.borrow();
        let points = slot.as_ref()?;
        points
            .point_reading_memory(memory)
            .into_iter()
            .chain(points.points_near_memory(memory))
            .find_map(|(selector, state)| {
                let load = scalar_read_in_state(read, state)?;
                Some((selector.clone(), state.clone(), load))
            })
    })
}

/// The name of the local that keeps `term` in its object at `pointer`, in
/// `state`: a borrowed Rust enum local `o` read there is spelled `o`. The
/// local's name reads its object at the point it was last written
/// ([`ExecutionState::held_local_value`]), so it spells exactly that read.
fn synthesize_held_value_local(
    term: &crate::kernel::AlgebraicTerm,
    pointer: &Pointer,
    state: &ExecutionState,
) -> Option<ContractExpression> {
    let (name, _, _) = state.locals().held_value_locals().find(|(_, _, slot)| {
        crate::instrumentation::record_deterministic_work(1);
        *slot == pointer
    })?;
    matches!(state.held_local_value(name), Some(ProgramValue::Parameter(held)) if held.as_ref() == term)
        .then(|| ContractExpression::ProgramExpression(ProgramExpression::Variable(name.to_string())))
}

/// `at(point, o)` for a read of a held-value local's object that no nearer
/// state names: the recorded point whose memory reads that version.
fn synthesize_recorded_held_value_local(
    term: &crate::kernel::AlgebraicTerm,
    pointer: &Pointer,
) -> Option<ContractExpression> {
    let crate::kernel::AlgebraicTermNode::MemoryLoad { memory, .. } = &term.node else {
        return None;
    };
    SYNTHESIS_RECORDED_POINTS.with(|slot| {
        let slot = slot.borrow();
        let points = slot.as_ref()?;
        points
            .point_reading_memory(memory)
            .into_iter()
            .chain(points.points_near_memory(memory))
            .find_map(|(selector, recorded)| {
                Some(ContractExpression::At {
                    selector: selector.clone(),
                    expression: Box::new(synthesize_held_value_local(term, pointer, recorded)?),
                })
            })
    })
}

/// `at(point, read)` for a load variable no nearer state names.
fn synthesize_load_at_recorded_point(
    variable: &Variable,
    parameter_binding: ParameterBinding<'_>,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let read = crate::kernel::registered_load_term_for_variable(variable)?;
    synthesize_read_at_recorded_point(&read, parameter_binding, bound_variables)
}

fn synthesize_read_at_recorded_point(
    read: &MachineTerm,
    parameter_binding: ParameterBinding<'_>,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let (selector, state, load) = recorded_point_of_load(read)?;
    let expression =
        synthesize_surface_bitvector(&load, parameter_binding, &state, bound_variables)?;
    Some(ContractExpression::At {
        selector,
        expression: Box::new(expression),
    })
}

/// The `at(<selector>, name)` spelling of a term the snapshot state's own
/// scalar local holds exactly. Only a term the current state cannot name
/// reaches this, so the snapshot spelling never shadows a current name.
fn synthesize_snapshot_local(term: &MachineTerm) -> Option<ContractExpression> {
    SYNTHESIS_SNAPSHOT_STATE.with(|slot| {
        let slot = slot.borrow();
        let (state, selector) = slot.as_ref()?;
        let name = state.locals().names_holding_integer(term).find(|name| {
            state.locals().get(name).is_some_and(|value| {
                crate::kernel::MachineIntegerType::from_program_type(value.program_type()).is_some()
            })
        })?;
        Some(ContractExpression::At {
            selector: selector.clone(),
            expression: Box::new(if crate::surface::is_click_value_name(name) {
                ContractExpression::CBinding(name.to_string())
            } else {
                ContractExpression::ProgramExpression(ProgramExpression::Variable(
                    surface_local_name(name).to_string(),
                ))
            }),
        })
    })
}

/// The `at(point, name)` spelling of a term a scalar local held at a
/// recorded point: the point where the value was introduced, found in one
/// index lookup. Only a term no nearer state names reaches this.
fn synthesize_recorded_local(term: &MachineTerm) -> Option<ContractExpression> {
    SYNTHESIS_RECORDED_POINTS.with(|slot| {
        let slot = slot.borrow();
        let (selector, name, _) = slot.as_ref()?.point_naming_integer(term)?;
        Some(ContractExpression::At {
            selector: selector.clone(),
            expression: Box::new(if crate::surface::is_click_value_name(name) {
                ContractExpression::CBinding(name.to_string())
            } else {
                ContractExpression::ProgramExpression(ProgramExpression::Variable(
                    surface_local_name(name).to_string(),
                ))
            }),
        })
    })
}

/// `at(point, e)` for a term a memory cell held at a recorded point, where
/// `e` spells it in that point's state: the field or element it is there.
/// The recorded points are cleared for the inner spelling, so it never
/// nests.
fn synthesize_recorded_cell_value(
    term: &MachineTerm,
    parameter_binding: ParameterBinding<'_>,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
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
        Some(ContractExpression::At {
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
    pointer: Pointer,
    state: usize,
    parameters: usize,
    arguments: usize,
    bound_variables: usize,
}

struct SurfacePointerFrame(PointerSynthesisKey);

impl SurfacePointerFrame {
    fn enter(
        pointer: &Pointer,
        parameter_binding: ParameterBinding<'_>,
        state: &ExecutionState,
        bound_variables: &BTreeMap<Variable, String>,
    ) -> Option<Self> {
        // All borrowed inputs remain live for this frame. Their addresses
        // distinguish snapshot and binder environments without cloning or
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

fn bitvector_term_exceeds_depth_limit(root: &MachineTerm) -> bool {
    let mut pending = vec![(root, 0usize)];
    while let Some((term, depth)) = pending.pop() {
        if depth >= SURFACE_SYNTHESIS_DEPTH_LIMIT.saturating_sub(1) {
            return true;
        }
        match term {
            crate::kernel::binary_machine_term!(left, right) => {
                pending.push((left, depth + 1));
                pending.push((right, depth + 1));
            }
            MachineTerm::Float32Binary { left, right, .. }
            | MachineTerm::Float64Binary { left, right, .. } => {
                pending.push((left, depth + 1));
                pending.push((right, depth + 1));
            }
            crate::kernel::unary_machine_term!(value) => {
                pending.push((value, depth + 1));
            }
            MachineTerm::If {
                then_term,
                else_term,
                ..
            } => {
                pending.push((then_term, depth + 1));
                pending.push((else_term, depth + 1));
            }
            MachineTerm::RangeFold {
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
            MachineTerm::PureFunctionApplication { arguments, .. } => {
                pending.extend(arguments.iter().map(|argument| (argument, depth + 1)));
            }
            MachineTerm::ClickFunctionApplication { .. }
            | MachineTerm::AlgebraicMatch { .. }
            | MachineTerm::IntegerToMachine { .. }
            | MachineTerm::BoolCast { .. } => {}
            MachineTerm::MemoryLoad(_, pointer, _) => {
                if let PointerOffsetTerm::Int32Scaled { value, .. }
                | PointerOffsetTerm::Int64Scaled { value, .. } = &pointer.offset
                {
                    pending.push((value.structural_value(), depth + 1));
                }
            }
            MachineTerm::PointerAddress(pointer, _) => {
                if let PointerOffsetTerm::Int32Scaled { value, .. }
                | PointerOffsetTerm::Int64Scaled { value, .. } = &pointer.offset
                {
                    pending.push((value.structural_value(), depth + 1));
                }
            }
            MachineTerm::Constant { .. } | MachineTerm::Variable(_) => {}
        }
    }
    false
}

pub(super) fn surface_synthesis_exhaustion_description() -> Option<String> {
    LAST_SURFACE_SYNTHESIS_EXHAUSTION.with(|last| {
        last.get().map(|category| {
            format!("Surface Click reconstruction exhausted its bounded {category} search")
        })
    })
}

pub(super) fn surface_synthesis_failure(prefix: &str, kernel: &Proposition) -> String {
    surface_synthesis_exhaustion_description()
        .map(|exhaustion| format!("{prefix}: {exhaustion}"))
        .unwrap_or_else(|| format!("{prefix}: {kernel:?}"))
}

pub(in crate::surface) fn synthesize_surface_proposition(
    proposition: &Proposition,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Option<ClickProposition> {
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
    store_index: &MachineTerm,
    cell_index: &MachineTerm,
    format: MachineIntegerType,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ClickProposition> {
    let _scope = SurfaceSynthesisScope::enter();
    let word = |term: &MachineTerm| {
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
            ContractExpression::Add(..)
                | ContractExpression::Subtract(..)
                | ContractExpression::Multiply(..)
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
    Some(ClickProposition::Comparison {
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
    term: &MachineTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Option<ContractExpression> {
    let _scope = SurfaceSynthesisScope::enter();
    synthesize_surface_bitvector(term, parameter_binding, state, &BTreeMap::new())
}

thread_local! {
    /// The kernel variables the proof's own binders (`let`, `choose`,
    /// `obtain`, `unfold`) name. A C local or parameter holding the same
    /// value is spelled first, since it carries its declared type; these
    /// name what no C name holds.
    static PROOF_BINDER_NAMES: std::cell::RefCell<std::sync::Arc<BTreeMap<Variable, String>>> =
        std::cell::RefCell::new(std::sync::Arc::default());
}

/// Runs `operation` with `names` as the proof binders' names; see
/// `PROOF_BINDER_NAMES`.
pub(in crate::surface) fn with_proof_binder_names<R>(
    names: std::sync::Arc<BTreeMap<Variable, String>>,
    operation: impl FnOnce() -> R,
) -> R {
    struct Restore(std::sync::Arc<BTreeMap<Variable, String>>);
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
        PersistentMap<String, ContractExpression>,
    )> = std::cell::RefCell::new((
        super::proof_object::binding_names::BindingNames::default(),
        PersistentMap::default(),
    ));
}

pub(super) struct ProofBindingNamesScope(
    super::proof_object::binding_names::BindingNames,
    PersistentMap<String, ContractExpression>,
);
impl ProofBindingNamesScope {
    pub(super) fn enter(
        names: super::proof_object::binding_names::BindingNames,
        shadows: PersistentMap<String, ContractExpression>,
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

fn proof_binder_name(variable: Variable) -> Option<String> {
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
    names: Vec<(ProgramValue, String)>,
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

/// A source expression for a semantic C value, such as a resource witness
/// inferred from memory: the proof local that names it, else a pointer or an
/// `int32` as the proof would write it at `state`.
fn synthesize_surface_pointer_address(
    pointer: &Pointer,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let operand =
        synthesize_surface_pointer_expression(pointer, parameter_binding, state, bound_variables)?;
    Some(crate::surface::lowering::contract_c_unary(
        operand,
        ProgramExpression::Cast {
            expression: Box::new(ProgramExpression::Value(ProgramValue::typed_pointer(
                pointer.clone(),
                ProgramType::VoidPointer,
            ))),
            target_type: ProgramType::UInt64,
            integer_mode: crate::kernel::IntegerCastMode::Standard,
            pointee_struct: None,
            pointee_volatile: false,
            pointee_constant: false,
            explicit_qualification: false,
        },
    ))
}

pub(in crate::surface) fn synthesize_surface_value(
    value: &ProgramValue,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Option<ContractExpression> {
    if let Some(name) = pointer_names::native_name(value) {
        return Some(ContractExpression::ProgramExpression(
            ProgramExpression::Variable(name),
        ));
    }
    if let Some(region) = SYNTHESIS_RECORDED_POINTS
        .with(|points| points.borrow().as_ref()?.read_event_naming_value(value))
    {
        return Some(ContractExpression::RegionResult(region));
    }
    let _scope = SurfaceSynthesisScope::enter();
    if crate::surface::diagnostics::exact_float_literal_spelling(value).is_some() {
        return Some(ContractExpression::ProgramExpression(
            ProgramExpression::Value(value.clone()),
        ));
    }
    match value {
        ProgramValue::Pointer(pointer) => synthesize_surface_pointer_expression(
            pointer.pointer(),
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
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ClickProposition> {
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
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ClickProposition> {
    let _scope = SurfaceSynthesisScope::enter();
    if let Proposition::MemoryLoadable { base, bytes, .. } = proposition {
        match synthesize_exact_external_zero_based_byte_range(
            base,
            bytes,
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
    names: &BTreeMap<Variable, String>,
) -> Option<ClickProposition> {
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
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ClickProposition> {
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
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ClickProposition> {
    let _frame = SurfaceSynthesisFrame::enter("proposition")?;
    match proposition {
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            let construct: fn(Box<ClickProposition>, Box<ClickProposition>) -> ClickProposition =
                match proposition {
                    Proposition::And(..) => ClickProposition::And,
                    Proposition::Or(..) => ClickProposition::Or,
                    Proposition::Implies(..) => ClickProposition::Implies,
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
    surface: &ClickProposition,
) -> Option<ClickProposition> {
    match (proposition, surface) {
        (
            Proposition::ForAll { body, .. },
            ClickProposition::ForAll {
                body: surface_body, ..
            },
        ) => {
            let body = omit_leading_definedness_spellings(body, surface_body)?;
            let ClickProposition::ForAll {
                click_type, name, ..
            } = surface
            else {
                unreachable!("surface universal matched above");
            };
            Some(ClickProposition::ForAll {
                click_type: click_type.clone(),
                name: name.clone(),
                written_name: None,
                body: Box::new(body),
            })
        }
        (
            Proposition::Exists { body, .. },
            ClickProposition::Exists {
                body: surface_body, ..
            },
        ) => {
            let body = omit_leading_definedness_spellings(body, surface_body)?;
            let ClickProposition::Exists {
                click_type, name, ..
            } = surface
            else {
                unreachable!("surface existential matched above");
            };
            Some(ClickProposition::Exists {
                click_type: click_type.clone(),
                name: name.clone(),
                written_name: None,
                body: Box::new(body),
            })
        }
        (Proposition::And(_, _), ClickProposition::And(_, _)) => {
            let mut proposition = proposition;
            let mut surface = surface;
            let mut omitted = false;
            while let Proposition::And(left, right) = proposition {
                if !is_leading_add_definedness_guard(left)
                    || !matches!(surface, ClickProposition::And(..))
                {
                    break;
                }
                let ClickProposition::And(_, surface_right) = surface else {
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
/// arithmetic guard fallback; callers with snapshot- or proof-local context
/// still perform their own authoritative re-lowering.
fn synthesized_surface_matches_proposition(
    candidate: &ClickProposition,
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
        state.memory(),
    );
    let (values, array_refs) = contract_environment_at_state(&parameter_values, &array_refs, state);
    let pointer_element_widths =
        crate::surface::lowering::parameter_pointer_element_widths(parameter_binding.parameters);
    let lowered = super::execution_planning::without_open_obligation_probe(|| {
        crate::surface::proof::fixed_state_proofs::lower_fixed_state_proposition_through_kernel_with(
            candidate,
            &PureFactContext::new(),
            ContractEnvironment::new(&values, &array_refs),
            FixedStateFrame::new(state, state, None, &RecordedSnapshots::default()),
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
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ClickProposition> {
    match proposition {
        Proposition::ForAll {
            var, sort, body, ..
        }
        | Proposition::Exists {
            var, sort, body, ..
        } => {
            let integer_type = sort.machine_integer_type()?;
            let click_type =
                ClickType::Program(crate::surface::generics::interface_type_from_program_type(
                    integer_type.program_type(),
                ));
            let conflicts = |candidate: &str| {
                parameter_binding
                    .parameters
                    .iter()
                    .any(|parameter| parameter.name() == candidate)
                    || state
                        .locals()
                        .object_values()
                        .any(|(name, _)| name == candidate)
                    || bound_variables.values().any(|name| name == candidate)
            };
            let written = SYNTHESIS_BINDER_NAMES.with(|slot| {
                slot.borrow()
                    .as_ref()
                    .and_then(|names| names.get(var).cloned())
            });
            let name = match written {
                Some(written) if !conflicts(&written) => written,
                _ => {
                    let mut suffix = bound_variables.len();
                    loop {
                        let candidate = format!("__click_q{suffix}");
                        if !conflicts(&candidate) {
                            break candidate;
                        }
                        suffix += 1;
                    }
                }
            };
            let mut body_variables = bound_variables.clone();
            body_variables.insert(*var, name.clone());
            let body = Box::new(synthesize_surface_proposition_with_bound_variables(
                body,
                parameter_binding,
                state,
                &body_variables,
            )?);
            Some(match proposition {
                Proposition::ForAll { .. } => ClickProposition::ForAll {
                    click_type: click_type.clone(),
                    name,
                    written_name: None,
                    body,
                },
                Proposition::Exists { .. } => ClickProposition::Exists {
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

/// `loadable(<base>[0..n])`: the whole named region, its byte count a
/// multiple of the `int32` cell the segment counts in. The start index is
/// zero, so the pointer's own offset is folded into the printed base.
fn synthesize_zero_based_loadable_segment(
    base: &Pointer,
    bytes: &MachineTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ClickProposition> {
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
        if !byte_count.is_multiple_of(4) {
            return None;
        }
        (
            ProgramExpression::Value(int32(byte_count / 4)),
            ProgramType::Int32Pointer,
        )
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
        // A byte extent remains unscaled over an explicit byte pointer.
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
        pointee_volatile: false,
        pointee_constant: false,
        explicit_qualification: false,
    };
    let surface_base = ContractExpression::ProgramExpression(semantic_base.clone());
    Some(ClickProposition::Loadable {
        segment: ContractSegment {
            uninitialized: false,
            state: ContractSegmentState::Current,
            base: semantic_base,
            start: ProgramExpression::Value(int32(0)),
            end: element_count.clone(),
            surface: ContractSegmentSurface::Range {
                base: surface_base,
                start: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(0))),
                end: ContractExpression::ProgramExpression(element_count),
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
    base: &Pointer,
    bytes: &MachineTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Result<Option<ClickProposition>, ()> {
    if base.block != PointerBlock::ExternalArgument {
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
            (pointer.pointer() == base && pointer.program_type().pointee_type()?.byte_width() == 1)
                .then(|| parameter.name().to_string())
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
    Ok(Some(ClickProposition::Loadable {
        segment: ContractSegment {
            uninitialized: false,
            state: ContractSegmentState::Current,
            base: named.clone(),
            start: start.clone(),
            end: end.clone(),
            surface: ContractSegmentSurface::Range {
                base: ContractExpression::ProgramExpression(named),
                start: ContractExpression::ProgramExpression(start),
                end: ContractExpression::ProgramExpression(end),
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
    base: &Pointer,
    bytes: &MachineTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ClickProposition> {
    if let Some(segment) = synthesize_struct_loadable_segment(base, bytes, parameter_binding, state)
    {
        return Some(segment);
    }
    // A one-element byte range is either the producer's folded representation
    // of `bytes[index..index + 1]` or its exact constant byte count. Handle it
    // before the historical folded-range paths so the source index comes from
    // the exact external parameter displacement rather than a same-block
    // inference.
    if base.block == PointerBlock::ExternalArgument
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
    let named_pointer_state = if base.block == PointerBlock::ExternalArgument
        && is_reduced_one_element_byte_count(bytes)
    {
        None
    } else {
        Some(state)
    };
    if let Some(byte_count) = bytes.as_const() {
        let (named, width, start) =
            named_range_bases(parameter_binding, named_pointer_state, state)
                .into_iter()
                .filter_map(|named| {
                    if named.pointer.offset == PointerOffsetTerm::Constant(0)
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
        let end = MachineTerm::add(start.clone(), MachineTerm::constant(element_count));
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
        return Some(ClickProposition::Loadable {
            segment: ContractSegment {
                uninitialized: false,
                state: ContractSegmentState::Current,
                base: named.lowered,
                start: start.clone(),
                end: end.clone(),
                surface: ContractSegmentSurface::Range {
                    base: named.surface,
                    start: ContractExpression::ProgramExpression(start),
                    end: ContractExpression::ProgramExpression(end),
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
    Some(ClickProposition::Loadable {
        segment: ContractSegment {
            uninitialized: false,
            state: ContractSegmentState::Current,
            base: named.lowered,
            start: start.clone(),
            end: end.clone(),
            surface: ContractSegmentSurface::Range {
                base: named.surface,
                start: ContractExpression::ProgramExpression(start),
                end: ContractExpression::ProgramExpression(end),
            },
        },
    })
}

/// Recover the written range for a one-element byte load emitted by
/// `loadable(bytes[index..index + 1])`. This is deliberately narrower than
/// `Pointer::element_index_from_base_with_width`: only a declared external
/// parameter, an exact direct displacement from that parameter's pointer, and
/// a one-byte element are authoritative enough to reconstruct the spelling.
/// The producer may retain either the exact constant `1` or the unreduced
/// `(index + 1) - index` form.
fn synthesize_external_symbolic_element_range(
    base: &Pointer,
    bytes: &MachineTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ClickProposition> {
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
                || named_base.pointer().block != PointerBlock::ExternalArgument
                || base.block != PointerBlock::ExternalArgument
            {
                return None;
            }
            let index = match &base.offset {
                PointerOffsetTerm::Add(left, right)
                    if left.as_ref() == &named_base.pointer().offset =>
                {
                    int32_scaled_value(right, 1)?
                }
                PointerOffsetTerm::Add(left, right)
                    if right.as_ref() == &named_base.pointer().offset =>
                {
                    int32_scaled_value(left, 1)?
                }
                // `bytes` itself can be at offset zero, in which case the
                // canonical pointer offset drops the zero-valued add.
                _ if named_base.pointer().offset == PointerOffsetTerm::Constant(0) => {
                    int32_scaled_value(&base.offset, 1)?
                }
                _ => return None,
            };
            let one_element = binary_node!(
                Int32,
                Subtract,
                Box::new(MachineTerm::add(index.clone(), MachineTerm::constant(1),)),
                Box::new(index.clone()),
            );
            if !matches!(bytes, bits32_constant!(1)) && bytes != &one_element {
                return None;
            }
            (!matches!(index, bits32_constant!(_))).then_some((parameter.name(), index))
        })?;
    if matches!(bytes, bits32_constant!(1)) {
        // Keep the byte count constant in the re-lowered proposition by
        // moving the symbolic index into the named pointer expression and
        // spelling a zero-based one-byte range over that displaced pointer.
        let semantic_base =
            synthesize_surface_pointer(base, parameter_binding, state, bound_variables)?;
        let surface_base = ContractExpression::ProgramExpression(semantic_base.clone());
        let start = ProgramExpression::Value(int32(0));
        let end = ProgramExpression::Value(int32(1));
        return Some(ClickProposition::Loadable {
            segment: ContractSegment {
                uninitialized: false,
                state: ContractSegmentState::Current,
                base: semantic_base,
                start: start.clone(),
                end: end.clone(),
                surface: ContractSegmentSurface::Range {
                    base: surface_base,
                    start: ContractExpression::ProgramExpression(start),
                    end: ContractExpression::ProgramExpression(end),
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
    let end_term = MachineTerm::add(index, MachineTerm::constant(1));
    let end = contract_expression_to_program_expression(&synthesize_surface_bitvector(
        &end_term,
        parameter_binding,
        state,
        bound_variables,
    )?)?;
    let named = ProgramExpression::Variable(surface_local_name(name).to_string());
    Some(ClickProposition::Loadable {
        segment: ContractSegment {
            uninitialized: false,
            state: ContractSegmentState::Current,
            base: named.clone(),
            start: start.clone(),
            end: end.clone(),
            surface: ContractSegmentSurface::Range {
                base: ContractExpression::ProgramExpression(named),
                start: ContractExpression::ProgramExpression(start),
                end: ContractExpression::ProgramExpression(end),
            },
        },
    })
}

fn is_reduced_one_element_byte_count(bytes: &MachineTerm) -> bool {
    let binary_term!(Int32, Subtract, end, start) = bytes else {
        return false;
    };
    *end.as_ref() == MachineTerm::add(start.as_ref().clone(), MachineTerm::constant(1))
}

fn is_one_element_byte_count(bytes: &MachineTerm) -> bool {
    matches!(bytes, bits32_constant!(1)) || is_reduced_one_element_byte_count(bytes)
}

fn int32_scaled_value(offset: &PointerOffsetTerm, width: i64) -> Option<MachineTerm> {
    match offset {
        PointerOffsetTerm::Int32Scaled { value, byte_width } if *byte_width == width => {
            Some(value.structural_value().clone())
        }
        _ => None,
    }
}

/// Every pointer this proof context can name, with the element width its
/// declared type steps by: the call's own parameters first, then the state's
/// pointer locals. The walk is over those two named lists only.
fn named_pointer_bases<'a>(
    parameter_binding: ParameterBinding<'a>,
    state: Option<&'a ExecutionState>,
) -> impl Iterator<Item = (String, crate::kernel::PointerValue, u32)> + 'a {
    parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
        .filter_map(|(parameter, argument)| {
            let ProgramExpression::Value(ProgramValue::Pointer(base)) = argument else {
                return None;
            };
            let width = parameter
                .interface_type()
                .pointee_type()?
                .to_kernel_type()
                .byte_width();
            Some((parameter.name().to_string(), base.clone(), width))
        })
        .chain(state.into_iter().flat_map(|state| {
            state.locals().object_values().filter_map(|(name, value)| {
                value.pointer()?;
                let native = value.native();
                let ProgramValue::Pointer(base) = native.as_ref() else {
                    return None;
                };
                let width = base.program_type().pointee_type()?.byte_width();
                Some((surface_local_name(name).to_string(), base.clone(), width))
            })
        }))
}

/// Synthesize the internal equation emitted when a memory read is assigned a
/// registered load identity. The variable is not a source-level identifier;
/// spell both sides through the registered pointer, anchored at the snapshot
/// named by the load.  Keeping this separate from ordinary bitvector
/// synthesis is important: the latter may deliberately resolve a load to a
/// current-state value, while this equation must retain its memory version.
fn synthesize_load_defining_equation(
    variable: &Variable,
    memory: &crate::kernel::SharedMemory,
    pointer: &Pointer,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ClickProposition> {
    let (registered_memory, registered_pointer) =
        crate::kernel::registered_load_for_variable(variable)?;
    // The defining equation carries the canonical snapshot that was recorded
    // with this variable. A merely equivalent load from another memory would
    // erase the epoch the equation is required to preserve.
    if registered_memory != *memory || registered_pointer != *pointer {
        return None;
    }

    let synthesize_at = |snapshot: &ExecutionState| {
        let load = registered_load_in_state(variable, snapshot)?;
        // Let the ordinary load spelling select a qualified source, an exact
        // local cell, a field, or the pointer/load fallback. It receives the
        // snapshot-specific load above, so the selected source cannot drift
        // to another epoch while the defining equation is presented.
        let left = synthesize_surface_bitvector(
            &MachineTerm::Variable(*variable),
            parameter_binding,
            snapshot,
            bound_variables,
        )?;
        let right =
            synthesize_surface_bitvector(&load, parameter_binding, snapshot, bound_variables)?;
        Some(ClickProposition::Comparison {
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
        return synthesize_at(&entry).map(|proposition| ClickProposition::At {
            selector: SnapshotSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Function,
                kind: ProgramPointKind::Entry,
            }),
            proposition: Box::new(proposition),
        });
    }
    SYNTHESIS_SNAPSHOT_STATE
        .with(|slot| {
            let slot = slot.borrow();
            let (snapshot, selector) = slot.as_ref()?;
            registered_load_in_state(variable, snapshot)?;
            synthesize_at(snapshot).map(|proposition| ClickProposition::At {
                selector: selector.clone(),
                proposition: Box::new(proposition),
            })
        })
        .or_else(|| {
            let read = crate::kernel::registered_load_term_for_variable(variable)?;
            let (selector, snapshot, _) = recorded_point_of_load(&read)?;
            synthesize_at(&snapshot).map(|proposition| ClickProposition::At {
                selector,
                proposition: Box::new(proposition),
            })
        })
}

// Large leaf temporaries must not occupy every recursive connective frame.
#[inline(never)]
/// Spell a logical Bool by its structure, including Bool operands of calls.
fn synthesize_surface_bool(
    condition: &ConditionTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let _frame = SurfaceSynthesisFrame::enter("bool")?;
    crate::instrumentation::record_deterministic_work(1);
    let operand = |condition: &ConditionTerm| {
        synthesize_surface_bool(condition, parameter_binding, state, bound_variables)
    };
    match condition {
        ConditionTerm::Constant(value) => Some(bool_literal(*value)),
        ConditionTerm::Variable(variable) => {
            if let Some(name) = folds::binder_name(false, *variable)
                .or_else(|| bound_variables.get(variable).cloned())
            {
                return Some(ContractExpression::Binding(name.clone()));
            }
            synthesize_surface_bitvector(
                &MachineTerm::bool_cast(MachineIntegerType::UInt8, condition.clone()),
                parameter_binding,
                state,
                bound_variables,
            )
        }
        ConditionTerm::BoolApplication(application) => synthesize_surface_call(
            application.name(),
            application.arguments(),
            parameter_binding,
            state,
            bound_variables,
        ),
        ConditionTerm::BoolIf {
            condition,
            then_condition,
            else_condition,
        } => Some(ContractExpression::If {
            condition: Box::new(bool_truth(operand(condition)?)),
            then_branch: Box::new(operand(then_condition)?),
            else_branch: Box::new(operand(else_condition)?),
        }),
        ConditionTerm::AlgebraicEqual(left, right) => {
            proposition_bool_value(ClickProposition::Comparison {
                left: synthesize_surface_algebraic(
                    left,
                    parameter_binding,
                    state,
                    bound_variables,
                )?,
                operator: ComparisonOperator::Equal,
                right: synthesize_surface_algebraic(
                    right,
                    parameter_binding,
                    state,
                    bound_variables,
                )?,
            })
            .ok()
        }
        ConditionTerm::BoolEqual(left, right) => {
            proposition_bool_value(ClickProposition::Comparison {
                left: operand(left)?,
                operator: ComparisonOperator::Equal,
                right: operand(right)?,
            })
            .ok()
        }
        _ => proposition_bool_value(synthesize_surface_atomic_proposition(
            &Proposition::ConditionIs(condition.clone(), true),
            parameter_binding,
            state,
            bound_variables,
        )?)
        .ok(),
    }
}

/// Whether `expression` reads a `bool` local of `state`, or reads one at a
/// recorded point.
fn names_bool_local(expression: &ContractExpression, state: &ExecutionState) -> bool {
    match expression {
        ContractExpression::ProgramExpression(ProgramExpression::Variable(name))
        | ContractExpression::CBinding(name) => state
            .locals()
            .get(name)
            .is_some_and(|value| value.program_type() == ProgramType::Bool),
        ContractExpression::At { expression, .. } => names_bool_local(expression, state),
        _ => false,
    }
}

fn synthesize_surface_atomic_proposition(
    proposition: &Proposition,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ClickProposition> {
    // A `bool` local's truth, C's test `w != 0` at `uint8` of its carrier:
    // the claim on the local, `w` or `not w`, which is what a claim on it
    // lowers to. Compared with an integer, as `w != 0`, it would not lower.
    if let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt8,
            relation: CompareRelation::Equal,
            left,
            right,
        },
        value,
    ) = proposition
        && right.bool_constant_value() == Some(false)
        && let Some(word) =
            synthesize_surface_bitvector(left, parameter_binding, state, bound_variables)
        && names_bool_local(&word, state)
    {
        let claim = crate::surface::bool_truth(word);
        return Some(if *value {
            ClickProposition::Not(Box::new(claim))
        } else {
            claim
        });
    }
    if let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        },
        true,
    ) = proposition
        && let (MachineTerm::Variable(variable), MachineTerm::MemoryLoad(memory, pointer, kind)) =
            (left.as_ref(), right.as_ref())
        && crate::kernel::is_load_variable(variable)
        && crate::kernel::registered_load_kind_for_variable(variable) == Some(*kind)
    {
        return synthesize_load_defining_equation(
            variable,
            memory,
            pointer,
            parameter_binding,
            state,
            bound_variables,
        );
    }
    if let Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) = proposition {
        return Some(ClickProposition::Comparison {
            left: synthesize_surface_algebraic(left, parameter_binding, state, bound_variables)?,
            operator: ComparisonOperator::Equal,
            right: synthesize_surface_algebraic(right, parameter_binding, state, bound_variables)?,
        });
    }
    if let Proposition::Equal(Term::Sequence(left), Term::Sequence(right)) = proposition {
        fn sequence(
            value: &crate::kernel::SequenceTerm,
            parameter_binding: ParameterBinding<'_>,
            state: &ExecutionState,
            bound: &BTreeMap<Variable, String>,
        ) -> Option<ContractExpression> {
            let _frame = SurfaceSynthesisFrame::enter("sequence")?;
            Some(match value.node.as_ref() {
                crate::kernel::SequenceTermNode::Literal(values) => {
                    ContractExpression::SequenceLiteral(
                        values
                            .iter()
                            .map(|value| {
                                let ProgramValue::Int32(value) = value else {
                                    return None;
                                };
                                synthesize_surface_bitvector(value, parameter_binding, state, bound)
                            })
                            .collect::<Option<Vec<_>>>()?,
                    )
                }
                crate::kernel::SequenceTermNode::Concat(left, right) => {
                    ContractExpression::SequenceConcat(
                        Box::new(sequence(left, parameter_binding, state, bound)?),
                        Box::new(sequence(right, parameter_binding, state, bound)?),
                    )
                }
            })
        }
        return Some(ClickProposition::Comparison {
            left: sequence(left, parameter_binding, state, bound_variables)?,
            operator: ComparisonOperator::Equal,
            right: sequence(right, parameter_binding, state, bound_variables)?,
        });
    }
    // A declared predicate call starts with its hidden logical resource-state
    // snapshot. Its source call does not write that argument. Each array-ref
    // argument then lowers to a (memory, pointer) term pair and each value
    // argument to a single value term, so the remaining kernel argument list
    // reads back unambiguously: a `Memory` term always opens an array-ref
    // pair. The snapshot the pair names is not written here — the current
    // memory needs no form, and every caller re-lowers the candidate and
    // compares it to the kernel fact, so a candidate built against the wrong
    // snapshot is rejected by that round trip rather than by a guess made
    // here.
    if let Proposition::Predicate {
        name,
        arguments: kernel_arguments,
    } = proposition
    {
        let mut call_arguments = Vec::new();
        let mut index = usize::from(matches!(
            kernel_arguments.first(),
            Some(Term::ExecutionState(_))
        ));
        while index < kernel_arguments.len() {
            match &kernel_arguments[index] {
                Term::Memory(_) => {
                    let Some(Term::ProgramValue(ProgramValue::Pointer(pointer))) =
                        kernel_arguments.get(index + 1)
                    else {
                        return None;
                    };
                    call_arguments.push(ContractExpression::ProgramExpression(
                        synthesize_surface_pointer(
                            pointer,
                            parameter_binding,
                            state,
                            bound_variables,
                        )?,
                    ));
                    index += 2;
                }
                Term::ProgramValue(ProgramValue::Pointer(pointer)) => {
                    call_arguments.push(ContractExpression::ProgramExpression(
                        synthesize_surface_pointer(
                            pointer,
                            parameter_binding,
                            state,
                            bound_variables,
                        )?,
                    ));
                    index += 1;
                }
                Term::ProgramValue(crate::kernel::int_promoted_c_value!(value)) => {
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
        return Some(ClickProposition::PredicateCall {
            name: crate::kernel::predicate_source_name(name)?.to_string(),
            arguments: call_arguments,
        });
    }
    if let Proposition::ResourceViewable { memory, resource } = proposition {
        let viewable = ClickProposition::ResourceViewable {
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
            SnapshotSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Function,
                kind: ProgramPointKind::Entry,
            })
        } else {
            SYNTHESIS_SNAPSHOT_STATE.with(|slot| {
                let slot = slot.borrow();
                let (snapshot, selector) = slot.as_ref()?;
                (snapshot.memory() == memory).then(|| selector.clone())
            })?
        };
        return Some(ClickProposition::At {
            selector,
            proposition: Box::new(viewable),
        });
    }
    if let Proposition::ResourceContains { parent, child } = proposition {
        return Some(ClickProposition::Contains {
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
        return Some(ClickProposition::Separate {
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
        memory,
        pointer,
        value_type,
    } = proposition
    {
        let pointer =
            synthesize_surface_pointer(pointer, parameter_binding, state, bound_variables)?;
        let validity = ClickProposition::Defined {
            expression: ContractExpression::ProgramExpression(ProgramExpression::TypedLoad {
                pointer: Box::new(pointer),
                value_type: *value_type,
                volatile: false,
                pointee_constant: false,
                access_class: None,
                source: crate::kernel::ExpressionLoadSource::none(),
            }),
        };
        if state.memory() == memory {
            return Some(validity);
        }
        let at_entry = SYNTHESIS_ENTRY_STATE.with(|slot| {
            slot.borrow()
                .as_ref()
                .is_some_and(|entry| entry.memory() == memory)
        });
        let selector = if at_entry {
            SnapshotSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Function,
                kind: ProgramPointKind::Entry,
            })
        } else {
            SYNTHESIS_SNAPSHOT_STATE.with(|slot| {
                let slot = slot.borrow();
                let (snapshot, selector) = slot.as_ref()?;
                (snapshot.memory() == memory).then(|| selector.clone())
            })?
        };
        return Some(ClickProposition::At {
            selector,
            proposition: Box::new(validity),
        });
    }
    if let Proposition::MemoryLoadable {
        memory,
        base,
        bytes,
        wide: false,
    } = proposition
    {
        let loadable = synthesize_zero_based_loadable_segment(
            base,
            bytes,
            parameter_binding,
            state,
            bound_variables,
        )
        .or_else(|| {
            synthesize_named_range_loadable_segment(
                base,
                bytes,
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
            return Some(ClickProposition::At {
                selector: SnapshotSelector::ProgramPoint(ProgramPointRef {
                    region: CodeRegionRef::Function,
                    kind: ProgramPointKind::Entry,
                }),
                proposition: Box::new(loadable),
            });
        }
        let snapshot_selector = SYNTHESIS_SNAPSHOT_STATE.with(|slot| {
            let slot = slot.borrow();
            let (snapshot, selector) = slot.as_ref()?;
            (snapshot.memory() == memory).then(|| selector.clone())
        });
        return Some(if let Some(selector) = snapshot_selector {
            ClickProposition::At {
                selector,
                proposition: Box::new(loadable),
            }
        } else {
            loadable
        });
    }
    if let Proposition::Not(body) = proposition {
        return Some(ClickProposition::Not(Box::new(
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
    if matches!(
        condition,
        ConditionTerm::Variable(_)
            | ConditionTerm::BoolApplication(_)
            | ConditionTerm::BoolIf { .. }
            | ConditionTerm::BoolEqual(..)
    ) {
        let claim = bool_truth(synthesize_surface_bool(
            condition,
            parameter_binding,
            state,
            bound_variables,
        )?);
        return Some(if *value {
            claim
        } else {
            ClickProposition::Not(Box::new(claim))
        });
    }
    if let ConditionTerm::Overflows {
        format: MachineIntegerType::Int32 | MachineIntegerType::Int64,
        op:
            op @ (OverflowOperation::Add | OverflowOperation::Subtract | OverflowOperation::Multiply),
        left,
        right,
    } = condition
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
            OverflowOperation::Add => ContractExpression::Add(left, right),
            OverflowOperation::Subtract => ContractExpression::Subtract(left, right),
            OverflowOperation::Multiply => ContractExpression::Multiply(left, right),
            _ => unreachable!("arithmetic overflow matched above"),
        };
        let defined = ClickProposition::Defined { expression };
        return Some(if *value {
            ClickProposition::Not(Box::new(defined))
        } else {
            defined
        });
    }
    if let ConditionTerm::Constant(condition) = condition {
        // A native equality folds to precisely this constant condition;
        // using != would instead change its polarity.
        let comparison = ClickProposition::Comparison {
            left: ContractExpression::IntegerLiteral("0".into()),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::IntegerLiteral(if *condition { "0" } else { "1" }.into()),
        };
        return Some(if *value {
            comparison
        } else {
            ClickProposition::Not(Box::new(comparison))
        });
    }
    if let ConditionTerm::PointerOffsetEqual(left, right) = condition {
        return Some(ClickProposition::Comparison {
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
    if let ConditionTerm::PointerValueEqual(left, right) = condition {
        return Some(ClickProposition::Comparison {
            left: synthesize_surface_pointer_expression(
                left.pointer(),
                parameter_binding,
                state,
                bound_variables,
            )?,
            operator: if *value {
                ComparisonOperator::Equal
            } else {
                ComparisonOperator::NotEqual
            },
            right: synthesize_surface_pointer_expression(
                right.pointer(),
                parameter_binding,
                state,
                bound_variables,
            )?,
        });
    }
    if let ConditionTerm::PointerEqual(left, right) = condition {
        let pointer = if **left == Pointer::null() || **right == Pointer::null() {
            synthesize_surface_pointer_expression
        } else {
            synthesize_surface_pointer_address
        };
        return Some(ClickProposition::Comparison {
            left: pointer(left, parameter_binding, state, bound_variables)?,
            operator: if *value {
                ComparisonOperator::Equal
            } else {
                ComparisonOperator::NotEqual
            },
            right: pointer(right, parameter_binding, state, bound_variables)?,
        });
    }
    if let Some(comparison) =
        synthesize_unsigned_comparison(condition, parameter_binding, state, bound_variables)
    {
        return Some(if *value {
            comparison
        } else {
            ClickProposition::Not(Box::new(comparison))
        });
    }
    // Arithmetic-producing comparisons keep machine Surface operands. Atomic
    // observations and casts still need explicit `to_integer`: re-lowering a
    // native atomic comparison would otherwise change its condition family.
    if !matches!(condition, ConditionTerm::Compare { .. })
        && let Some(view) =
            crate::kernel::machine_integer::comparison::structural_comparison_view(condition)
        && matches!(
            view.format,
            MachineIntegerType::Int32
                | MachineIntegerType::UInt32
                | MachineIntegerType::Int64
                | MachineIntegerType::UInt64
        )
        && view.operands.iter().any(|operand| {
            matches!(
                operand.operand_view().binary(),
                Some((
                    _,
                    MachineBinaryOp::Add
                        | MachineBinaryOp::Subtract
                        | MachineBinaryOp::Multiply
                        | MachineBinaryOp::Divide
                        | MachineBinaryOp::Remainder
                        | MachineBinaryOp::ShiftLeft
                        | MachineBinaryOp::ShiftRight,
                    _
                ))
            )
        })
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
        let comparison = ClickProposition::Comparison {
            left: raise(&view.operands[0])?,
            operator,
            right: raise(&view.operands[1])?,
        };
        return Some(if *value != view.negated {
            comparison
        } else {
            ClickProposition::Not(Box::new(comparison))
        });
    }
    let integer_comparison = match condition {
        ConditionTerm::IntegerLessThan(left, right) => {
            Some((left, ComparisonOperator::LessThan, right))
        }
        ConditionTerm::IntegerLessEqual(left, right) => {
            Some((left, ComparisonOperator::LessEqual, right))
        }
        ConditionTerm::IntegerGreaterThan(left, right) => {
            Some((left, ComparisonOperator::GreaterThan, right))
        }
        ConditionTerm::IntegerGreaterEqual(left, right) => {
            Some((left, ComparisonOperator::GreaterEqual, right))
        }
        ConditionTerm::IntegerEqual(left, right) => Some((left, ComparisonOperator::Equal, right)),
        ConditionTerm::IntegerNotEqual(left, right) => {
            Some((left, ComparisonOperator::NotEqual, right))
        }
        _ => None,
    };
    if let Some((left, operator, right)) = integer_comparison {
        let comparison = ClickProposition::Comparison {
            // A rewrite may have removed the last typed operand. Retain
            // mathematical context without relying on an ambient binding.
            left: integer_typed_expression(synthesize_surface_integer(
                left,
                parameter_binding,
                state,
                bound_variables,
            )?),
            operator,
            right: synthesize_surface_integer(right, parameter_binding, state, bound_variables)?,
        };
        return Some(if *value {
            comparison
        } else {
            ClickProposition::Not(Box::new(comparison))
        });
    }
    // A native 8- or 16-bit comparison is spelled as the Integer comparison
    // of its operands' values, which lowers back to it (the Integer form of
    // exact observations of one format is its native comparison).
    if let ConditionTerm::Compare {
        format:
            format @ (MachineIntegerType::Int8
            | MachineIntegerType::UInt8
            | MachineIntegerType::Int16
            | MachineIntegerType::UInt16),
        relation,
        left,
        right,
    } = condition
    {
        let observe = |term: &MachineTerm| -> Option<crate::kernel::SharedIntegerTerm> {
            crate::kernel::IntegerTerm::from_machine(*format, term.clone()).map(Into::into)
        };
        let (l, r) = (observe(left)?, observe(right)?);
        let integer = match relation {
            CompareRelation::LessThan => ConditionTerm::IntegerLessThan(l, r),
            CompareRelation::LessEqual => ConditionTerm::IntegerLessEqual(l, r),
            CompareRelation::GreaterThan => ConditionTerm::IntegerGreaterThan(l, r),
            CompareRelation::GreaterEqual => ConditionTerm::IntegerGreaterEqual(l, r),
            CompareRelation::Equal => ConditionTerm::IntegerEqual(l, r),
        };
        return synthesize_surface_atomic_proposition(
            &Proposition::ConditionIs(integer, *value),
            parameter_binding,
            state,
            bound_variables,
        );
    }
    let (left, operator, right) = match condition {
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
        } => (left, ComparisonOperator::LessThan, right),
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
        } => (left, ComparisonOperator::LessEqual, right),
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
        } => (left, ComparisonOperator::GreaterThan, right),
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
        } => (left, ComparisonOperator::GreaterEqual, right),
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
        } => (left, ComparisonOperator::Equal, right),
        _ => return None,
    };
    // An `int32` order reads its operands' words as `int32`. An operand
    // spelled in `uint32` (a `uint32` local or parameter whose word a sign
    // cast compared signed) would make the spelled comparison unsigned, a
    // different fact, so it is written converted, as `u as int32 < 0`.
    let signed_order = matches!(
        condition,
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan
                | CompareRelation::LessEqual
                | CompareRelation::GreaterThan
                | CompareRelation::GreaterEqual,
            ..
        }
    );
    let operand = |term: &MachineTerm| {
        // Wide comparisons retain signedness at each read and operation.
        // Reconstruct their shared operands rather than defaulting a Bits64
        // read to int64 before an unsigned operation consumes it.
        let expression = if let ConditionTerm::Compare {
            format: format @ (MachineIntegerType::Int64 | MachineIntegerType::UInt64),
            ..
        } = condition
        {
            let root = crate::kernel::KernelTermImport::default().machine(*format, term);
            raise_kernel_term(&root, parameter_binding, state, bound_variables)?
        } else {
            synthesize_surface_bitvector(term, parameter_binding, state, bound_variables)?
        };
        if signed_order
            && (bitvector_spells_uint32(term, parameter_binding, state, bound_variables)
                || matches!(
                    expression,
                    ContractExpression::Add(..)
                        | ContractExpression::Subtract(..)
                        | ContractExpression::Multiply(..)
                ))
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
    let comparison = ClickProposition::Comparison {
        left: surface_left?,
        operator,
        right: surface_right?,
    };
    if *value {
        Some(comparison)
    } else if operator == ComparisonOperator::Equal {
        let ClickProposition::Comparison { left, right, .. } = comparison else {
            unreachable!()
        };
        Some(ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::NotEqual,
            right,
        })
    } else {
        Some(ClickProposition::Not(Box::new(comparison)))
    }
}

/// The value is outside the binding's scope, so this local name cannot
/// capture a name in the expression being spelled.
pub(super) fn integer_typed_expression(value: ContractExpression) -> ContractExpression {
    ContractExpression::Let {
        name: "integer_value".into(),
        click_type: Some(ClickType::Integer),
        value: Box::new(value),
        body: Box::new(ContractExpression::Binding("integer_value".into())),
    }
}

/// An Integer arithmetic term over machine observations, spelled with
/// `to_integer` around each observation and named truncating operations.
/// Opaque specification applications retain their source boundary.
fn synthesize_surface_integer(
    term: &crate::kernel::IntegerTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let term = crate::kernel::KernelTermImport::default().integer(&term.clone().into());
    raise_kernel_term(&term, parameter_binding, state, bound_variables)
}

// Keep this construction outside the recursive general dispatch frame.
fn raise_algebraic_if<'a>(
    arguments: &'a [crate::kernel::KernelTerm; 3],
    mut raise: impl FnMut(&'a crate::kernel::KernelTerm) -> Option<SurfaceTerm>,
) -> Option<SurfaceTerm> {
    Some(SurfaceTerm::If {
        condition: Box::new(bool_truth(raise(&arguments[0])?)),
        then_branch: Box::new(raise(&arguments[1])?),
        else_branch: Box::new(raise(&arguments[2])?),
    })
}

/// The shared term-to-surface boundary. Arithmetic and calls have common
/// children; the legacy leaf dispatch is temporary and never projects away
/// part of a value. Fold bodies retain their typed lexical scope.
pub(super) fn raise_kernel_term(
    term: &crate::kernel::KernelTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<SurfaceTerm> {
    use crate::kernel::{KernelIntegerOperator as Op, KernelTermNode as Node, KernelType};
    let category = if term.ty() == &KernelType::Integer {
        "integer"
    } else {
        "function-call"
    };
    let _frame = SurfaceSynthesisFrame::enter(category)?;
    let recurse = |term| raise_kernel_term(term, parameter_binding, state, bound_variables);
    if matches!(
        term.node(),
        Node::MachineBinary { .. }
            | Node::MachineUnary { .. }
            | Node::MachineCast { .. }
            | Node::MachineIf { .. }
    ) && let Some(named) =
        synthesize_named_integer_local(state.locals().names_holding_kernel_integer(term))
    {
        return Some(named);
    }
    Some(match term.node() {
        Node::Fold(fold) => folds::raise_fold(fold, parameter_binding, state, bound_variables)?,
        Node::Match(matched) => {
            matches::raise_match(matched, parameter_binding, state, bound_variables)?
        }
        Node::Constructor(_) | Node::AlgebraicRead(_) => {
            let argument = crate::kernel::KernelTermExport::default()
                .argument(term)
                .ok()?;
            synthesize_legacy_call_argument(&argument, parameter_binding, state, bound_variables)?
        }
        Node::Variable(_) if matches!(term.ty(), KernelType::Algebraic(_)) => {
            let argument = crate::kernel::KernelTermExport::default()
                .argument(term)
                .ok()?;
            synthesize_legacy_call_argument(&argument, parameter_binding, state, bound_variables)?
        }
        Node::IntegerLiteral(value) if value.sign() == num_bigint::Sign::Minus => {
            SurfaceTerm::Negate(Box::new(SurfaceTerm::IntegerLiteral((-value).to_string())))
        }
        Node::IntegerLiteral(value) => SurfaceTerm::IntegerLiteral(value.to_string()),
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
                Some(name) => SurfaceTerm::Binding(name),
                // A loop's pass count past the loop.
                None => SurfaceTerm::Binding(crate::surface::loop_iterations_spelling(
                    SYNTHESIS_RECORDED_POINTS
                        .with(|slot| slot.borrow().as_ref()?.loop_naming_iterations(*variable))?,
                )),
            }
        }
        Node::AlgebraicIf { arguments } => raise_algebraic_if(arguments, recurse)?,
        Node::IntegerIf { arguments } => SurfaceTerm::If {
            condition: Box::new(bool_truth(recurse(&arguments[0])?)),
            then_branch: Box::new(integer_typed_expression(recurse(&arguments[1])?)),
            else_branch: Box::new(integer_typed_expression(recurse(&arguments[2])?)),
        },
        Node::IntegerOperation {
            operator,
            arguments,
        } => {
            let mut arguments = arguments
                .iter()
                .map(recurse)
                .collect::<Option<Vec<_>>>()?
                .into_iter();
            let left = arguments.next()?;
            match operator {
                Op::Negate => SurfaceTerm::Negate(Box::new(integer_typed_expression(left))),
                Op::Add => SurfaceTerm::Add(Box::new(left), Box::new(arguments.next()?)),
                Op::Subtract => SurfaceTerm::Subtract(Box::new(left), Box::new(arguments.next()?)),
                Op::Multiply => SurfaceTerm::Multiply(Box::new(left), Box::new(arguments.next()?)),
                Op::TruncatingQuotient | Op::TruncatingRemainder => SurfaceTerm::Call {
                    name: if *operator == Op::TruncatingQuotient {
                        "truncating_quotient"
                    } else {
                        "truncating_remainder"
                    }
                    .into(),
                    arguments: vec![left, arguments.next()?],
                },
            }
        }
        Node::AlgebraicCall(call) => SurfaceTerm::Call {
            name: generic_instance_source_name(&call.name).into(),
            arguments: call
                .arguments
                .iter()
                .map(recurse)
                .collect::<Option<Vec<_>>>()?,
        },
        Node::Call { name, arguments } => {
            let call = SurfaceTerm::Call {
                name: generic_instance_source_name(name).into(),
                arguments: arguments.iter().map(recurse).collect::<Option<Vec<_>>>()?,
            };
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
        Node::BoolIf { arguments } | Node::MachineIf { arguments } => SurfaceTerm::If {
            condition: Box::new(bool_truth(recurse(&arguments[0])?)),
            then_branch: Box::new(recurse(&arguments[1])?),
            else_branch: Box::new(recurse(&arguments[2])?),
        },
        Node::BoolEqual { arguments } => proposition_bool_value(ClickProposition::Comparison {
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
            proposition_bool_value(ClickProposition::Comparison {
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
            let operand =
                |term| synthesize_observation_operand(recurse(term)?, format.program_type());
            proposition_bool_value(ClickProposition::Comparison {
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
        Node::BoolRead(_)
        | Node::AlgebraicEqual { .. }
        | Node::BoolOverflow { .. }
        | Node::PointerValueEqual(_)
        | Node::PointerEqual { .. }
        | Node::PointerOffsetEqual { .. }
        | Node::LegacyBool(_) => {
            let condition = crate::kernel::KernelTermExport::condition(term).ok()?;
            synthesize_surface_bool(&condition, parameter_binding, state, bound_variables)?
        }
        Node::Variable(variable) if term.ty() == &KernelType::Bool => synthesize_surface_bool(
            &ConditionTerm::Variable(*variable),
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
        } => SurfaceTerm::Call {
            name: integer_conversion_name(*destination).into(),
            arguments: vec![recurse(operand)?],
        },
        Node::MachineObservation { format, operand } => {
            let expression = recurse(operand)?;
            SurfaceTerm::Call {
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
        Node::PointerCall { call, .. } => recurse(call)?,
        Node::ArrayReference {
            memory, pointer, ..
        } => synthesize_at_memory(memory, state, |selected| {
            raise_kernel_term(pointer, parameter_binding, selected, bound_variables)
        })?,

        Node::PointerRead { value, .. }
        | Node::PointerArithmetic { value, .. }
        | Node::PointerValue(value) => {
            if let Some(name) = pointer_names::shared_name(value) {
                SurfaceTerm::ProgramExpression(ProgramExpression::Variable(name))
            } else {
                synthesize_surface_value(term.pointer_native()?, parameter_binding, state)?
            }
        }
        Node::Legacy(legacy) => match legacy.value() {
            crate::kernel::PureFunctionArgument::Integer(value) => {
                let mut import = crate::kernel::KernelTermImport::default();
                if let Some(matched) =
                    crate::kernel::KernelMatch::import_integer(&mut import, value)
                {
                    matches::raise_match(&matched, parameter_binding, state, bound_variables)?
                } else {
                    let fold = crate::kernel::KernelFold::import_integer(&mut import, value)?;
                    folds::raise_fold(&fold, parameter_binding, state, bound_variables)?
                }
            }
            value => {
                synthesize_legacy_call_argument(value, parameter_binding, state, bound_variables)?
            }
        },
        Node::FloatLiteral { .. } => SurfaceTerm::ProgramExpression(ProgramExpression::Value(
            crate::kernel::KernelTermExport::float(term).ok()?,
        )),
        Node::MachineLiteral(literal) => {
            let KernelType::Program(ty) = term.ty() else {
                return None;
            };
            SurfaceTerm::ProgramExpression(ProgramExpression::Value(
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
                MachineBinaryOp::Add => SurfaceTerm::Add(left, right),
                MachineBinaryOp::Subtract => SurfaceTerm::Subtract(left, right),
                MachineBinaryOp::Multiply => SurfaceTerm::Multiply(left, right),
                MachineBinaryOp::Divide => SurfaceTerm::Divide(left, right),
                MachineBinaryOp::Remainder => SurfaceTerm::Remainder(left, right),
                MachineBinaryOp::ShiftLeft => SurfaceTerm::ShiftLeft(left, right),
                MachineBinaryOp::ShiftRight => SurfaceTerm::ShiftRight(left, right),
                MachineBinaryOp::BitwiseAnd => SurfaceTerm::BitwiseAnd(left, right),
                MachineBinaryOp::BitwiseOr => SurfaceTerm::BitwiseOr(left, right),
                MachineBinaryOp::BitwiseXor => SurfaceTerm::BitwiseXor(left, right),
            }
        }
        Node::MachineUnary { operand, .. } => SurfaceTerm::BitwiseNot(Box::new(recurse(operand)?)),
        Node::PointerAddress { .. } => {
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
                        MachineTerm::MemoryLoad(_, _, crate::kernel::LoadKind::Bits64)
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
        Node::Variable(variable) => synthesize_surface_bitvector(
            &MachineTerm::Variable(*variable),
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
                SurfaceTerm::CUnary {
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

/// Keep the observation's interpretation inside its snapshot selector.
fn synthesize_observation_operand(
    expression: SurfaceTerm,
    format: ProgramType,
) -> Option<SurfaceTerm> {
    Some(match expression {
        SurfaceTerm::At {
            selector,
            expression,
        } => SurfaceTerm::At {
            selector,
            expression: Box::new(synthesize_observation_operand(*expression, format)?),
        },
        SurfaceTerm::Old(expression) => SurfaceTerm::Old(Box::new(synthesize_observation_operand(
            *expression,
            format,
        )?)),
        expression => SurfaceTerm::CUnary {
            operand: Box::new(expression),
            // CUnary's Surface operand is authoritative. A C fragment
            // would discard resource fields and scoped binding information.
            lowered: ProgramExpression::Cast {
                expression: Box::new(ProgramExpression::Value(int32(0))),
                target_type: format,
                integer_mode: crate::kernel::IntegerCastMode::CConversion,
                pointee_struct: None,
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
/// order. A comparison with a snapshot-relative operand has no spelling
/// here.
fn synthesize_unsigned_comparison(
    condition: &ConditionTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ClickProposition> {
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
        CompareRelation::LessThan => ComparisonOperator::LessThan,
        CompareRelation::LessEqual => ComparisonOperator::LessEqual,
        CompareRelation::GreaterThan => ComparisonOperator::GreaterThan,
        CompareRelation::GreaterEqual => ComparisonOperator::GreaterEqual,
        CompareRelation::Equal => return None,
    };
    let (left, right) = (left.as_ref(), right.as_ref());
    // The `uint32` local holding the operand, named directly: a signed local
    // can hold the same bits, and its name would make the comparison signed.
    let operand = |term: &MachineTerm| match term.as_const() {
        Some(_) => Some(ContractExpression::ProgramExpression(
            ProgramExpression::Value(ProgramValue::UInt32(term.clone())),
        )),
        None => state
            .locals()
            .names_holding_integer(term)
            .find(|name| {
                *name != "result"
                    && *name != crate::kernel::C_CONTRACT_RESULT_NAME
                    && state.locals().get(name).is_some_and(|value| {
                        value.program_type() == crate::kernel::ProgramType::UInt32
                            && value
                                .native_payload()
                                .is_none_or(|native| matches!(native, ProgramValue::UInt32(_)))
                    })
            })
            .map(|name| {
                ContractExpression::ProgramExpression(ProgramExpression::Variable(
                    surface_local_name(name).to_string(),
                ))
            })
            .or_else(|| {
                let expression =
                    synthesize_surface_bitvector(term, parameter_binding, state, bound_variables)?;
                // A snapshot-relative operand is left to the diagnostic
                // renderer, which spells it in its snapshot, preserving
                // loop-ranking observations and refusal diagnostics.
                // Division/remainder still cast within their own snapshot
                // when reconstructing those operations.
                if matches!(
                    expression,
                    ContractExpression::At { .. } | ContractExpression::Old(_)
                ) {
                    return None;
                }
                synthesize_uint32_operand(expression)
            }),
    };
    Some(ClickProposition::Comparison {
        left: operand(left)?,
        operator,
        right: operand(right)?,
    })
}

pub(super) fn synthesize_surface_resource_subject(
    resource: &Resource,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
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
    let Resource::Memory(range) = resource else {
        return None;
    };
    // A scalar's storage is its address, not its current value or the zero
    // offset within its block. The slot index supplies the exact local name.
    let surface_base = if let Some(name) = state.locals().name_for_slot(range.base()) {
        let object = ProgramExpression::Variable(surface_local_name(name).to_string());
        let address = if state.locals().array_object_element_type(name).is_some() {
            object
        } else {
            ProgramExpression::AddressOf(Box::new(object))
        };
        ContractExpression::ProgramExpression(address)
    } else {
        synthesize_surface_pointer_expression(
            range.base(),
            parameter_binding,
            state,
            bound_variables,
        )?
    };
    // A range counts its retained element width, which need not be the
    // pointee width of the name (for example, a struct field's backing).
    // Spell scalar coordinates explicitly; pointer casts retain provenance.
    let scalar_pointer_type = match range.element_width() {
        1 => Some(ProgramType::UInt8Pointer),
        2 => Some(ProgramType::UInt16Pointer),
        4 => Some(ProgramType::Int32Pointer),
        8 => Some(ProgramType::UInt64Pointer),
        _ => None,
    };
    let surface_base = match scalar_pointer_type {
        Some(target_type) => ContractExpression::CUnary {
            operand: Box::new(surface_base),
            lowered: ProgramExpression::Cast {
                expression: Box::new(ProgramExpression::Value(int32(0))),
                target_type,
                integer_mode: crate::kernel::IntegerCastMode::Standard,
                pointee_struct: None,
                pointee_volatile: false,
                pointee_constant: false,
                explicit_qualification: false,
            },
        },
        None => surface_base,
    };
    // The bounds are spelled as the terms they are, in either index kind.
    let (range_start, range_end) = range.bound_terms();
    let surface_start =
        synthesize_surface_bitvector(range_start, parameter_binding, state, bound_variables)?;
    let surface_end =
        synthesize_surface_bitvector(range_end, parameter_binding, state, bound_variables)?;
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

/// Spells one certified equality whose operands were read from different
/// snapshots, such as a callee postcondition relating a cell after
/// the call to its value before it. Each operand is anchored at the first
/// listed point where it denotes a source expression; the caller lists the
/// recorded statement entries nearest first and must re-lower the result to
/// confirm it denotes exactly this kernel fact.
pub(in crate::surface) fn synthesize_surface_equality_across_points(
    proposition: &Proposition,
    parameter_binding: ParameterBinding<'_>,
    points: &[(ProgramPointRef, &ExecutionState)],
) -> Option<ClickProposition> {
    let _scope = SurfaceSynthesisScope::enter();
    let Proposition::ConditionIs(condition, true) = proposition else {
        return None;
    };
    let bound_variables = BTreeMap::new();
    let anchored = |synthesize: &dyn Fn(&ExecutionState) -> Option<ContractExpression>| {
        points
            .iter()
            .take_while(|_| !crate::instrumentation::deadline_exceeded())
            .find_map(|(point, state)| {
                let expression = synthesize(state)?;
                Some(ContractExpression::At {
                    selector: SnapshotSelector::ProgramPoint(point.clone()),
                    expression: Box::new(expression),
                })
            })
    };
    let (left, right) = match condition {
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
        } => (
            anchored(&|state| {
                synthesize_surface_bitvector(left, parameter_binding, state, &bound_variables)
            })?,
            anchored(&|state| {
                synthesize_surface_bitvector(right, parameter_binding, state, &bound_variables)
            })?,
        ),
        ConditionTerm::PointerOffsetEqual(left, right) => (
            anchored(&|state| {
                synthesize_surface_pointer_offset(left, parameter_binding, state, &bound_variables)
            })?,
            anchored(&|state| {
                synthesize_surface_pointer_offset(right, parameter_binding, state, &bound_variables)
            })?,
        ),
        ConditionTerm::PointerValueEqual(left, right) => (
            anchored(&|state| {
                synthesize_surface_pointer_expression(
                    left.pointer(),
                    parameter_binding,
                    state,
                    &bound_variables,
                )
            })?,
            anchored(&|state| {
                synthesize_surface_pointer_expression(
                    right.pointer(),
                    parameter_binding,
                    state,
                    &bound_variables,
                )
            })?,
        ),
        ConditionTerm::PointerEqual(left, right) => (
            anchored(&|state| {
                synthesize_surface_pointer_address(left, parameter_binding, state, &bound_variables)
            })?,
            anchored(&|state| {
                synthesize_surface_pointer_address(
                    right,
                    parameter_binding,
                    state,
                    &bound_variables,
                )
            })?,
        ),
        _ => return None,
    };
    Some(ClickProposition::Comparison {
        left,
        operator: ComparisonOperator::Equal,
        right,
    })
}

/// Whether a parameter's bare name still means the value it was passed: false
/// once the function has reassigned it, when the bare name means the new value
/// and the passed one is spelled at function entry instead.
fn parameter_names_its_argument(
    name: &str,
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
    term: &PointerOffsetTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let _frame = SurfaceSynthesisFrame::enter("pointer-offset")?;
    for (parameter, argument) in parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
    {
        if let ProgramExpression::Value(ProgramValue::Pointer(pointer)) = argument
            && pointer.offset == *term
            && parameter_names_its_argument(parameter.name(), argument, state)
        {
            return Some(ContractExpression::ProgramExpression(
                ProgramExpression::Variable(parameter.name().to_string()),
            ));
        }
    }
    if let Some(field) = synthesize_parameter_field_pointer_value(term, parameter_binding, state) {
        return Some(field);
    }
    match term {
        PointerOffsetTerm::Add(left, right) => {
            let indexed_pointer = |base: &PointerOffsetTerm, byte_offset: &PointerOffsetTerm| {
                let PointerOffsetTerm::Constant(byte_offset) = byte_offset else {
                    return None;
                };
                if byte_offset % 4 != 0 {
                    return None;
                }
                let ContractExpression::ProgramExpression(base) =
                    synthesize_surface_pointer_offset(
                        base,
                        parameter_binding,
                        state,
                        bound_variables,
                    )?
                else {
                    return None;
                };
                Some(ContractExpression::ProgramExpression(
                    ProgramExpression::Add(
                        Box::new(base),
                        Box::new(ProgramExpression::Value(ProgramValue::Int32(
                            MachineTerm::constant((byte_offset / 4) as u32),
                        ))),
                    ),
                ))
            };
            let dynamically_indexed_pointer =
                |base: &PointerOffsetTerm, index: &PointerOffsetTerm| {
                    let PointerOffsetTerm::Int32Scaled {
                        value: index,
                        byte_width: 4,
                    } = index
                    else {
                        return None;
                    };
                    let base = contract_expression_to_program_expression(
                        &synthesize_surface_pointer_offset(
                            base,
                            parameter_binding,
                            state,
                            bound_variables,
                        )?,
                    )?;
                    let index =
                        contract_expression_to_program_expression(&synthesize_surface_bitvector(
                            index.structural_value(),
                            parameter_binding,
                            state,
                            bound_variables,
                        )?)?;
                    Some(ContractExpression::ProgramExpression(
                        ProgramExpression::Add(Box::new(base), Box::new(index)),
                    ))
                };
            indexed_pointer(left, right)
                .or_else(|| indexed_pointer(right, left))
                .or_else(|| dynamically_indexed_pointer(left, right))
                .or_else(|| dynamically_indexed_pointer(right, left))
        }
        PointerOffsetTerm::Int32Scaled { value, byte_width } if matches!(*byte_width, 1 | 4) => {
            synthesize_surface_bitvector(
                value.structural_value(),
                parameter_binding,
                state,
                bound_variables,
            )
        }
        PointerOffsetTerm::Constant(_)
        | PointerOffsetTerm::Variable(_)
        | PointerOffsetTerm::Int32Scaled { .. }
        | PointerOffsetTerm::Int64Scaled { .. } => None,
    }
}

/// Names a canonical pointer value through a currently readable pointer field
/// of a struct parameter. Allocation identity conditions compare canonical
/// allocation offsets, not the memory-load syntax that produced them; this
/// reverse lookup recovers stable source syntax at each recorded snapshot.
fn synthesize_parameter_field_pointer_value(
    term: &PointerOffsetTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Option<ContractExpression> {
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
                ExpressionOutcome::Value(ProgramValue::Int32(value)) => {
                    PointerOffsetTerm::scale_int32(
                        value,
                        i64::from(value_type.pointee_type()?.byte_width()),
                    )
                }
                _ => continue,
            };
            if !crate::kernel::offsets_have_same_canonical_form(&loaded_offset, term) {
                continue;
            }
            let base_expression = ProgramExpression::Variable(parameter.name().to_string());
            let lowered_pointer = if field.offset_bytes() == 0 {
                base_expression.clone()
            } else {
                ProgramExpression::PointerOffsetBytes {
                    pointer: Box::new(base_expression.clone()),
                    bytes: field.offset_bytes(),
                }
            };
            return Some(ContractExpression::Field {
                pointee_struct: None,
                base: Box::new(ContractExpression::ProgramExpression(base_expression)),
                field: field_name.clone(),
                lowered: ProgramExpression::TypedLoad {
                    pointer: Box::new(lowered_pointer),
                    value_type,
                    volatile: false,
                    pointee_constant: field.pointee_is_constant(),
                    access_class: None,
                    source: Default::default(),
                },
                offset_bytes: field.offset_bytes(),
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
                ExpressionOutcome::Value(ProgramValue::Int32(value)) => {
                    PointerOffsetTerm::scale_int32(
                        value,
                        i64::from(value_type.pointee_type()?.byte_width()),
                    )
                }
                _ => continue,
            };
            if !crate::kernel::offsets_have_same_canonical_form(&loaded_offset, term) {
                continue;
            }
            return Some(ContractExpression::Field {
                pointee_struct: None,
                base: Box::new(ContractExpression::ProgramExpression(owner.base.clone())),
                field: field_name.clone(),
                lowered: ProgramExpression::TypedLoad {
                    pointer: Box::new(owner_field_pointer(&owner.base, field.offset_bytes())),
                    value_type,
                    volatile: false,
                    pointee_constant: field.pointee_is_constant(),
                    access_class: None,
                    source: Default::default(),
                },
                offset_bytes: field.offset_bytes(),
            });
        }
    }
    None
}

/// Compatibility entry for pointer carriers still registered under a name.
fn registered_load_in_state(variable: &Variable, state: &ExecutionState) -> Option<MachineTerm> {
    let read = crate::kernel::registered_load_term_for_variable(variable)?;
    scalar_read_in_state(&read, state)
}

fn scalar_read_in_state(read: &MachineTerm, state: &ExecutionState) -> Option<MachineTerm> {
    let MachineTerm::MemoryLoad(_, pointer, kind) = read else {
        return None;
    };
    let memory = crate::kernel::intern_memory_ref(state.memory());
    let selected =
        crate::kernel::canonical_form_of_load(memory.clone(), pointer.as_ref().clone(), *kind);
    (selected == *read).then(|| MachineTerm::MemoryLoad(memory, pointer.clone(), *kind))
}

// Unsigned division and remainder use the usual C conversion of both
// operands when either operand is uint32. Keep an explicit snapshot outside
// the cast so reconstruction never silently changes which memory is read.
fn synthesize_uint32_operand(expression: ContractExpression) -> Option<ContractExpression> {
    synthesize_observation_operand(expression, ProgramType::UInt32)
}

/// `expression` converted to `int32`, inside its snapshot selector: the
/// signed counterpart of [`synthesize_uint32_operand`].
fn synthesize_int32_operand(expression: ContractExpression) -> Option<ContractExpression> {
    synthesize_observation_operand(expression, ProgramType::Int32)
}

/// Whether [`synthesize_surface_bitvector`] spells `term` as a `uint32`
/// expression: by the name of a `uint32` local or parameter, or as
/// arithmetic the usual conversions make `uint32` because one operand is.
/// It follows that function's choice of name, so it reads one local or
/// parameter per name in the term.
fn bitvector_spells_uint32(
    term: &MachineTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> bool {
    if let MachineTerm::Variable(variable) = term
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
    let either = |left: &MachineTerm, right: &MachineTerm| {
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
        MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            to: MachineIntegerType::UInt32,
            ..
        } => true,
        _ => false,
    }
}

/// A population's count at function entry, which the kernel holds as an
/// opaque symbol, is spelled `old(count(R(anchor, _, ...)))`. A fact the
/// kernel records about it, such as the bound a consumed member places on
/// it, then has a source spelling and can be cited.
fn synthesize_population_entry_count(
    term: &MachineTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Option<ContractExpression> {
    let MachineTerm::Variable(variable) = term else {
        return None;
    };
    let population = state.population_with_entry_count(*variable)?;
    let [AlgebraicValue::Program(ProgramValue::Pointer(anchor))] = population.arguments() else {
        return None;
    };
    let anchor = synthesize_surface_pointer_expression(
        anchor.pointer(),
        parameter_binding,
        state,
        &BTreeMap::new(),
    )?;
    let wildcards = population.population_arity().map_or(0, |arity| arity - 1);
    let arguments = std::iter::once(anchor)
        .chain(std::iter::repeat_n(
            ContractExpression::ResourceWildcard,
            wildcards,
        ))
        .collect();
    Some(ContractExpression::Old(Box::new(
        ContractExpression::ResourceCount(Box::new(ResourceClause::Declared {
            type_schema: None,
            resource_type_arguments: Vec::new(),
            resource_arguments: Vec::new(),
            access: ResourceAccessMode::Own,
            kind: ResourceKind::Token,
            name: population.family().to_string(),
            arguments,
            parameter_types: Vec::new(),
        })),
    )))
}

fn synthesize_named_integer_local<'a>(
    mut holders: impl Iterator<Item = &'a str>,
) -> Option<SurfaceTerm> {
    if let Some(name) = holders.next() {
        return Some(if name == crate::kernel::C_CONTRACT_RESULT_NAME {
            ContractExpression::ProgramExpression(ProgramExpression::Variable("result".to_string()))
        } else if crate::surface::is_click_value_name(name) {
            ContractExpression::CBinding(name.to_string())
        } else {
            ContractExpression::ProgramExpression(ProgramExpression::Variable(
                surface_local_name(name).to_string(),
            ))
        });
    }
    None
}

/// A retained word read carries its interpretation. Spell that exact typed
/// load, at the same selected snapshot, instead of a signed load followed by
/// an unsigned cast (which introduces a different observation node).
fn synthesize_typed_word_read(
    read: &MachineTerm,
    value_type: ProgramType,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let MachineTerm::MemoryLoad(memory, pointer, kind) = read else {
        return None;
    };
    let read =
        crate::kernel::canonical_form_of_load(memory.clone(), pointer.as_ref().clone(), *kind);
    let at_state = |load: &MachineTerm, state: &ExecutionState| {
        let MachineTerm::MemoryLoad(_, pointer, _) = load else {
            return None;
        };
        let address = synthesize_surface_pointer_expression(
            pointer,
            parameter_binding,
            state,
            bound_variables,
        )?;
        Some(ContractExpression::CUnary {
            operand: Box::new(address),
            lowered: ProgramExpression::TypedLoad {
                pointer: Box::new(ProgramExpression::Value(int32(0))),
                value_type,
                volatile: false,
                pointee_constant: false,
                access_class: None,
                source: Default::default(),
            },
        })
    };
    if let Some(load) = scalar_read_in_state(&read, state) {
        return at_state(&load, state);
    }
    if let Some(entry) = SYNTHESIS_ENTRY_STATE.with(|slot| slot.borrow().clone())
        && let Some(load) = scalar_read_in_state(&read, &entry)
    {
        return Some(ContractExpression::Old(Box::new(at_state(&load, &entry)?)));
    }
    let (selector, recorded, load) = recorded_point_of_load(&read)?;
    Some(ContractExpression::At {
        selector,
        expression: Box::new(at_state(&load, &recorded)?),
    })
}

fn synthesize_surface_bitvector(
    term: &MachineTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let _frame = SurfaceSynthesisFrame::enter("bitvector")?;
    let bitvector_frame = SurfaceBitvectorFrame::enter();
    if bitvector_frame.is_outermost() && bitvector_term_exceeds_depth_limit(term) {
        record_surface_synthesis_exhaustion("bitvector");
        return None;
    }
    if let MachineTerm::Variable(variable) = term
        && let Some(name) =
            folds::binder_name(false, *variable).or_else(|| bound_variables.get(variable).cloned())
    {
        return Some(ContractExpression::ProgramExpression(
            ProgramExpression::Variable(name.clone()),
        ));
    }
    if let int32_constant!(_) = term {
        return Some(ContractExpression::ProgramExpression(
            ProgramExpression::Value(ProgramValue::Int32(term.clone())),
        ));
    }
    // A `uint32` constant keeps its format, so an operator over it spells
    // and lowers back at `uint32`.
    if let uint32_constant!(_) = term {
        return Some(ContractExpression::ProgramExpression(
            ProgramExpression::Value(ProgramValue::UInt32(term.clone())),
        ));
    }
    if let Some(named) = synthesize_named_integer_local(state.locals().names_holding_integer(term))
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
            ContractExpression::At {
                selector: SnapshotSelector::ProgramPoint(ProgramPointRef {
                    region: CodeRegionRef::Function,
                    kind: ProgramPointKind::Entry,
                }),
                expression: Box::new(if crate::surface::is_click_value_name(&name) {
                    ContractExpression::CBinding(name)
                } else {
                    ContractExpression::ProgramExpression(ProgramExpression::Variable(name))
                }),
            }
        } else if crate::surface::is_click_value_name(&name) {
            ContractExpression::CBinding(name)
        } else {
            ContractExpression::ProgramExpression(ProgramExpression::Variable(name))
        });
    }
    if let MachineTerm::Variable(variable) = term
        && let Some(name) = proof_binder_name(*variable)
    {
        return Some(ContractExpression::ProgramExpression(
            ProgramExpression::Variable(name),
        ));
    }
    if let Some(region) = SYNTHESIS_RECORDED_POINTS
        .with(|points| points.borrow().as_ref()?.read_event_naming_scalar(term))
    {
        return Some(ContractExpression::RegionResult(region));
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
        return Some(ContractExpression::RegionResult(region));
    }
    if let Some(field) = synthesize_local_aggregate_field(term, state) {
        return Some(field);
    }
    if let Some(field) = synthesize_local_struct_pointer_field(term, parameter_binding, state) {
        return Some(field);
    }
    if let Some(snapshot) = synthesize_snapshot_local(term) {
        return Some(snapshot);
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
    let binary = |left: &MachineTerm, right: &MachineTerm| {
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
        // The 32-bit widening of a narrow value is written as the
        // conversion it is (`c as int32`, `c as uint32`).
        MachineTerm::Cast {
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
        MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            value,
            to: destination,
            ..
        } => {
            let operand =
                synthesize_surface_bitvector(value, parameter_binding, state, bound_variables)?;
            Some(ContractExpression::CUnary {
                operand: Box::new(operand),
                lowered: ProgramExpression::Cast {
                    expression: Box::new(ProgramExpression::Value(int32(0))),
                    target_type: destination.program_type(),
                    integer_mode: crate::kernel::IntegerCastMode::CConversion,
                    pointee_struct: None,
                    pointee_volatile: false,
                    pointee_constant: false,
                    explicit_qualification: false,
                },
            })
        }
        MachineTerm::BoolCast { to, value } => {
            // synthesize_surface_bool uses the uint8 carrier to name an
            // unbound Bool variable. Naming above exhausted that route;
            // do not recurse back into the same unnamed variable.
            if *to == MachineIntegerType::UInt8
                && matches!(value.as_ref(), ConditionTerm::Variable(variable) if !bound_variables.contains_key(variable))
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
            Some(ContractExpression::ProgramExpression(
                ProgramExpression::Value(value),
            ))
        }
        bits32_constant!(_) => {
            unreachable!("constants returned above")
        }
        binary_term!(Bits32, Add, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Add(left, right))
        }
        binary_term!(Bits32, Subtract, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Subtract(left, right))
        }
        binary_term!(Bits32, Multiply, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Multiply(left, right))
        }
        binary_term!(Int32, Divide, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Divide(left, right))
        }
        binary_term!(UInt32, Divide, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Divide(
                left,
                Box::new(synthesize_uint32_operand(*right)?),
            ))
        }
        binary_term!(Int32, Remainder, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Remainder(left, right))
        }
        binary_term!(UInt32, Remainder, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Remainder(
                left,
                Box::new(synthesize_uint32_operand(*right)?),
            ))
        }
        binary_term!(Bits32, ShiftLeft, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::ShiftLeft(left, right))
        }
        binary_term!(Int32, ShiftRight, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::ShiftRight(left, right))
        }
        binary_term!(UInt32, ShiftRight, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::ShiftRight(left, right))
        }
        binary_term!(Bits32, BitwiseAnd, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::BitwiseAnd(left, right))
        }
        binary_term!(Bits32, BitwiseOr, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::BitwiseOr(left, right))
        }
        binary_term!(Bits32, BitwiseXor, left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::BitwiseXor(left, right))
        }
        unary_term!(Bits32, BitwiseNot, value) => Some(ContractExpression::BitwiseNot(Box::new(
            synthesize_surface_bitvector(value, parameter_binding, state, bound_variables)?,
        ))),
        // Floating-point operation terms are not integer surface fragments;
        // callers that need them retain the original C expression instead.
        MachineTerm::Float32Negate(_)
        | MachineTerm::Float32Binary { .. }
        | MachineTerm::Float64Negate(_)
        | MachineTerm::Float64Binary { .. } => None,
        MachineTerm::PointerAddress(pointer, _) => {
            let pointer =
                synthesize_surface_pointer(pointer, parameter_binding, state, bound_variables)?;
            Some(ContractExpression::ProgramExpression(
                ProgramExpression::Cast {
                    expression: Box::new(pointer),
                    target_type: ProgramType::UInt64,
                    integer_mode: crate::kernel::IntegerCastMode::Standard,
                    pointee_struct: None,
                    pointee_volatile: false,
                    pointee_constant: false,
                    explicit_qualification: false,
                },
            ))
        }
        MachineTerm::MemoryLoad(memory, kernel_pointer, kind) => {
            let read = crate::kernel::canonical_form_of_load(
                memory.clone(),
                kernel_pointer.as_ref().clone(),
                *kind,
            );
            let old = SYNTHESIS_ENTRY_STATE
                .with(|slot| slot.borrow().clone())
                .and_then(|entry| {
                    if entry.memory() == state.memory() {
                        return None;
                    }
                    let load = scalar_read_in_state(&read, &entry)?;
                    if scalar_read_in_state(&read, state).is_some() {
                        return None;
                    }
                    Some(ContractExpression::Old(Box::new(
                        synthesize_surface_bitvector(
                            &load,
                            parameter_binding,
                            &entry,
                            bound_variables,
                        )?,
                    )))
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
                return Some(ContractExpression::Index(
                    Box::new(field),
                    Box::new(ContractExpression::ProgramExpression(
                        ProgramExpression::Value(int32(0)),
                    )),
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
                return Some(ContractExpression::ProgramExpression(
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
                return Some(ContractExpression::ProgramExpression(
                    ProgramExpression::Variable(name),
                ));
            }
            if let PointerBlock::Concrete(block) = &kernel_pointer.block
                && let Some(name) = block.strip_prefix("local:")
                && kernel_pointer.offset == PointerOffsetTerm::Constant(0)
                && state
                    .locals()
                    .scalar_object_type(name)
                    .is_some_and(|ty| ty.pointee_type().is_none())
            {
                // A memory-resident scalar local reads as its own name.
                Some(ContractExpression::ProgramExpression(
                    ProgramExpression::Variable(name.to_string()),
                ))
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
                        let element_type = parameter.interface_type().pointee_type()?;
                        kernel_pointer.element_index_from_base_with_width(
                            base,
                            element_type.to_kernel_type().byte_width(),
                        )?;
                        Some(element_type.to_kernel_type())
                    });
                let pointer = synthesize_surface_pointer(
                    kernel_pointer,
                    parameter_binding,
                    state,
                    bound_variables,
                );
                let pointer = pointer?;
                // An unsigned byte read is spelled as one whatever the
                // pointer's own element type: through a signed plain `char`
                // pointer it is the byte's one name, not the pointer's read.
                // When no pointee type was recovered, the pointer's spelling
                // must not choose the access width. A word read states its
                // own type, including through byte-addressed struct fields.
                let typed_word = value_type.is_none() && *kind == crate::kernel::LoadKind::Int32;
                let value_type = if *kind == crate::kernel::LoadKind::UInt8 {
                    Some(ProgramType::UInt8)
                } else if typed_word {
                    Some(ProgramType::Int32)
                } else {
                    value_type
                };
                Some(ContractExpression::ProgramExpression(match value_type {
                    Some(value_type) if value_type == ProgramType::UInt8 || typed_word => {
                        ProgramExpression::TypedLoad {
                            pointer: Box::new(pointer),
                            value_type,
                            volatile: false,
                            pointee_constant: false,
                            access_class: None,
                            source: Default::default(),
                        }
                    }
                    _ => ProgramExpression::Load(Box::new(pointer)),
                }))
            }
        }
        // A load variable names one cell of one memory version. It denotes
        // the source load of that cell from any snapshot whose memory
        // lies in the same epoch; the kernel's own naming law decides that,
        // so the spelling lowers back to exactly this variable there.
        MachineTerm::Variable(variable) => {
            // A recorded load already supplies the address to inspect. Avoid
            // searching unrelated locals when ordinary certificates name it.
            if let Some((_, pointer)) = crate::kernel::registered_load_for_variable(variable)
                && let Some(name) =
                    state.local_name_holding_bitvector_variable_at(*variable, &pointer)
            {
                return Some(ContractExpression::ProgramExpression(
                    ProgramExpression::Variable(name.to_string()),
                ));
            }
            // A memory-resident scalar local holding exactly this variable
            // reads as its own name here. Looking for aliases is a bounded
            // smart search; a simple certificate never scans unrelated slots.
            if crate::instrumentation::smart_tactic_active()
                && !STRUCTURAL_GOAL_SYNTHESIS.with(|slot| slot.get())
                && let Some(name) = state.local_name_holding_bitvector_variable(*variable)
            {
                return Some(ContractExpression::ProgramExpression(
                    ProgramExpression::Variable(name.to_string()),
                ));
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
                    Some(ContractExpression::Old(Box::new(
                        synthesize_surface_bitvector(
                            &load,
                            parameter_binding,
                            entry,
                            bound_variables,
                        )?,
                    )))
                })
                .or_else(|| {
                    synthesize_load_at_recorded_point(variable, parameter_binding, bound_variables)
                })
        }
        int64_constant!(value) => Some(ContractExpression::ProgramExpression(
            ProgramExpression::Value(ProgramValue::Int64(MachineTerm::int64_constant(
                constant_i64(*value),
            ))),
        )),
        uint64_constant!(value) => Some(ContractExpression::ProgramExpression(
            ProgramExpression::Value(ProgramValue::UInt64(MachineTerm::uint64_constant(
                constant_u64(*value),
            ))),
        )),
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
            Some(ContractExpression::CUnary {
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
                    pointee_volatile: false,
                    pointee_constant: false,
                    explicit_qualification: false,
                },
            })
        }
        cast_term!(UInt32From64, value) => Some(ContractExpression::CUnary {
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
                pointee_volatile: false,
                pointee_constant: false,
                explicit_qualification: false,
            },
        }),
        MachineTerm::Binary {
            op, left, right, ..
        } => {
            let (left, right) = binary(left, right)?;
            Some(match op {
                MachineBinaryOp::Add => ContractExpression::Add(left, right),
                MachineBinaryOp::Subtract => ContractExpression::Subtract(left, right),
                MachineBinaryOp::Multiply => ContractExpression::Multiply(left, right),
                MachineBinaryOp::Divide => ContractExpression::Divide(left, right),
                MachineBinaryOp::Remainder => ContractExpression::Remainder(left, right),
                MachineBinaryOp::ShiftLeft => ContractExpression::ShiftLeft(left, right),
                MachineBinaryOp::ShiftRight => ContractExpression::ShiftRight(left, right),
                MachineBinaryOp::BitwiseAnd => ContractExpression::BitwiseAnd(left, right),
                MachineBinaryOp::BitwiseOr => ContractExpression::BitwiseOr(left, right),
                MachineBinaryOp::BitwiseXor => ContractExpression::BitwiseXor(left, right),
            })
        }
        MachineTerm::Unary {
            op: crate::kernel::MachineUnaryOp::BitwiseNot,
            operand,
            ..
        } => Some(ContractExpression::BitwiseNot(Box::new(
            synthesize_surface_bitvector(operand, parameter_binding, state, bound_variables)?,
        ))),
        MachineTerm::If {
            condition,
            then_term,
            else_term,
        } => Some(ContractExpression::If {
            condition: Box::new(synthesize_surface_proposition_with_bound_variables(
                &Proposition::ConditionIs((**condition).clone(), true),
                parameter_binding,
                state,
                bound_variables,
            )?),
            then_branch: Box::new(synthesize_surface_bitvector(
                then_term,
                parameter_binding,
                state,
                bound_variables,
            )?),
            else_branch: Box::new(synthesize_surface_bitvector(
                else_term,
                parameter_binding,
                state,
                bound_variables,
            )?),
        }),
        MachineTerm::RangeFold { .. } => {
            folds::raise_machine_fold(term, parameter_binding, state, bound_variables)
        }
        MachineTerm::PureFunctionApplication {
            name,
            arguments: values,
        } => Some(ContractExpression::Call {
            name: name.clone(),
            arguments: values
                .iter()
                .map(|value| {
                    synthesize_surface_bitvector(value, parameter_binding, state, bound_variables)
                })
                .collect::<Option<Vec<_>>>()?,
        }),
        MachineTerm::ClickFunctionApplication {
            name,
            arguments: values,
        } => synthesize_surface_call(name, values, parameter_binding, state, bound_variables),
        MachineTerm::IntegerToMachine { value, destination } => {
            let operand = crate::kernel::KernelTermImport::default().integer(value);
            let term = crate::kernel::KernelTerm::integer_to_machine(*destination, operand).ok()?;
            raise_kernel_term(&term, parameter_binding, state, bound_variables)
        }
        MachineTerm::AlgebraicMatch { .. } => {
            matches::raise_machine_match(term, parameter_binding, state, bound_variables)
        }
    }
}

/// Restore explicit calls in invariant-body goals so their defining equations
/// can be opened by ordinary `unfold`. Array snapshots are named only when
/// they are exactly the current or function-entry snapshot; no frame search
/// or memory-content comparison is used to choose the spelling.
#[inline(never)]
fn synthesize_surface_call(
    name: &str,
    values: &[crate::kernel::PureFunctionArgument],
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let _frame = SurfaceSynthesisFrame::enter("function-call")?;
    let mut importer = crate::kernel::KernelTermImport::default();
    let arguments = values
        .iter()
        .map(|value| {
            if !consume_surface_synthesis_work("function-argument") {
                return None;
            }
            raise_kernel_term(
                &importer.argument(value),
                parameter_binding,
                state,
                bound_variables,
            )
        })
        .collect::<Option<Vec<_>>>()?;
    Some(SurfaceTerm::Call {
        name: generic_instance_source_name(name).into(),
        arguments,
    })
}

/// A snapshot-bearing argument selects its memory by identity. An intermediate
/// recorded snapshot is as explicit as `old`; no timeline or frame search is
/// needed to recover that snapshot's source selector.
fn synthesize_at_memory(
    memory: &crate::kernel::SharedMemory,
    state: &ExecutionState,
    raise: impl Fn(&ExecutionState) -> Option<SurfaceTerm>,
) -> Option<SurfaceTerm> {
    if *memory == crate::kernel::intern_memory_ref(state.memory()) {
        return raise(state);
    }
    if let Some(entry) = SYNTHESIS_ENTRY_STATE.with(|slot| slot.borrow().clone())
        && *memory == crate::kernel::intern_memory_ref(entry.memory())
    {
        return Some(SurfaceTerm::Old(Box::new(raise(&entry)?)));
    }
    let (selector, recorded) = SYNTHESIS_RECORDED_POINTS.with(|slot| {
        let slot = slot.borrow();
        let (selector, recorded) = slot.as_ref()?.point_reading_memory(memory)?;
        Some((selector.clone(), recorded.clone()))
    })?;
    Some(SurfaceTerm::At {
        selector,
        expression: Box::new(raise(&recorded)?),
    })
}

fn synthesize_legacy_call_argument(
    value: &crate::kernel::PureFunctionArgument,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<SurfaceTerm> {
    Some(match value {
        crate::kernel::PureFunctionArgument::Value(value @ ProgramValue::Pointer(_)) => {
            SurfaceTerm::ProgramExpression(ProgramExpression::Variable(pointer_names::native_name(
                value,
            )?))
        }
        crate::kernel::PureFunctionArgument::Value(ProgramValue::Bool(word)) => {
            synthesize_surface_bool(
                &ConditionTerm::truth_of_bool_word(word),
                parameter_binding,
                state,
                bound_variables,
            )?
        }
        crate::kernel::PureFunctionArgument::Value(
            value @ (ProgramValue::Float32(_) | ProgramValue::Float64(_)),
        ) if crate::surface::diagnostics::exact_float_literal_spelling(value).is_some() => {
            SurfaceTerm::ProgramExpression(ProgramExpression::Value(value.clone()))
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
        crate::kernel::PureFunctionArgument::Integer(value) => {
            synthesize_surface_integer(value, parameter_binding, state, bound_variables)?
        }
        crate::kernel::PureFunctionArgument::Algebraic(value) => {
            synthesize_surface_algebraic(value, parameter_binding, state, bound_variables)?
        }
        crate::kernel::PureFunctionArgument::ArrayRef {
            memory,
            pointer: ProgramValue::Pointer(pointer),
            ..
        } => synthesize_at_memory(
            &crate::kernel::intern_memory_ref(memory),
            state,
            |selected| {
                synthesize_surface_pointer_expression(
                    pointer,
                    parameter_binding,
                    selected,
                    bound_variables,
                )
            },
        )?,
        _ => return None,
    })
}

fn synthesize_parameter_field_indexed_int32_load(
    pointer: &Pointer,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let _frame = SurfaceSynthesisFrame::enter("indexed-field")?;
    let pointer_field_and_index = |base: &PointerOffsetTerm,
                                   index: Option<&PointerOffsetTerm>|
     -> Option<(ContractExpression, ContractExpression)> {
        let PointerOffsetTerm::Int32Scaled {
            value,
            byte_width: 4,
        } = base
        else {
            return None;
        };
        // The field's value is its load, or the load variable naming that
        // load at this state.
        let named_load = match value.structural_value() {
            MachineTerm::Variable(variable) => registered_load_in_state(variable, state),
            _ => None,
        };
        let MachineTerm::MemoryLoad(_, field_pointer, _) =
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
        let index = match index {
            None => ContractExpression::ProgramExpression(ProgramExpression::Value(int32(0))),
            Some(PointerOffsetTerm::Int32Scaled {
                value,
                byte_width: 4,
            }) => synthesize_surface_bitvector(
                value.structural_value(),
                parameter_binding,
                state,
                bound_variables,
            )?,
            Some(PointerOffsetTerm::Constant(bytes)) if bytes % 4 == 0 => {
                ContractExpression::ProgramExpression(ProgramExpression::Value(int32(
                    u32::try_from(bytes / 4).ok()?,
                )))
            }
            Some(_) => return None,
        };
        Some((field, index))
    };
    let (field, index) = match &pointer.offset {
        base @ (PointerOffsetTerm::Int32Scaled { .. } | PointerOffsetTerm::Int64Scaled { .. }) => {
            pointer_field_and_index(base, None)?
        }
        PointerOffsetTerm::Add(left, right) => pointer_field_and_index(left, Some(right))
            .or_else(|| pointer_field_and_index(right, Some(left)))?,
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => return None,
    };
    // Preserve array indexing for a declared int32 pointer, including fields
    // reached through automatic struct-pointer locals. Their layout is already
    // indexed by local name in the function's synthesis scope.
    if let ContractExpression::Field {
        base, field: name, ..
    } = &field
        && let ContractExpression::ProgramExpression(ProgramExpression::Variable(owner)) =
            base.as_ref()
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
            .find(|parameter| parameter.name() == owner)
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
            return Some(ContractExpression::Index(Box::new(field), Box::new(index)));
        }
    }
    // The kernel indexed a four-byte scalar. The field's written C type
    // may instead be a pointer to a struct, whose indexing scales by that
    // struct's size. Spell the address through the supported byte view and
    // retain the scalar load's width explicitly.
    let bytes = ContractExpression::CUnary {
        lowered: ProgramExpression::Cast {
            expression: Box::new(contract_expression_to_program_expression(&field)?),
            target_type: ProgramType::UInt8Pointer,
            integer_mode: crate::kernel::IntegerCastMode::Standard,
            pointee_struct: None,
            pointee_volatile: false,
            pointee_constant: false,
            explicit_qualification: false,
        },
        operand: Box::new(field),
    };
    let address = ContractExpression::Add(
        Box::new(bytes),
        Box::new(ContractExpression::Multiply(
            Box::new(index),
            Box::new(ContractExpression::ProgramExpression(
                ProgramExpression::Value(int32(4)),
            )),
        )),
    );
    Some(ContractExpression::CUnary {
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

/// A scalar field of a struct-pointer local whose cell currently holds
/// `term`, spelled `local->field`. The layouts come from the installed local
/// layout scope; without one, no local is a candidate.
fn synthesize_local_struct_pointer_field(
    term: &MachineTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Option<ContractExpression> {
    for owner in struct_owners(parameter_binding, state) {
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
            return Some(ContractExpression::Field {
                pointee_struct: None,
                base: Box::new(ContractExpression::ProgramExpression(owner.base.clone())),
                field: field_name.clone(),
                lowered: ProgramExpression::TypedLoad {
                    pointer: Box::new(owner_field_pointer(&owner.base, field.offset_bytes())),
                    value_type,
                    volatile: false,
                    pointee_constant: field.pointee_is_constant(),
                    access_class: None,
                    source: Default::default(),
                },
                offset_bytes: field.offset_bytes(),
            });
        }
    }
    None
}

fn synthesize_local_aggregate_field(
    term: &MachineTerm,
    state: &ExecutionState,
) -> Option<ContractExpression> {
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
                        Pointer {
                            block: slot.block.clone(),
                            offset: crate::kernel::PointerOffsetTerm::add(
                                slot.offset.clone(),
                                crate::kernel::PointerOffsetTerm::constant(i64::from(
                                    element_offset,
                                )),
                            ),
                        }
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
                    let base = ProgramExpression::Variable(surface_local_name(name).to_string());
                    let lowered_pointer = if field.offset_bytes() == 0 {
                        base.clone()
                    } else {
                        ProgramExpression::PointerOffsetBytes {
                            pointer: Box::new(base.clone()),
                            bytes: field.offset_bytes(),
                        }
                    };
                    let field_expression = ContractExpression::Field {
                        pointee_struct: None,
                        base: Box::new(ContractExpression::ProgramExpression(base)),
                        field: field.name().to_string(),
                        lowered: ProgramExpression::TypedLoad {
                            pointer: Box::new(lowered_pointer),
                            value_type: field.program_type(),
                            volatile: false,
                            pointee_constant: false,
                            access_class: None,
                            source: Default::default(),
                        },
                        offset_bytes: field.offset_bytes(),
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
                        let ContractExpression::Field { lowered, .. } = &field_expression else {
                            unreachable!()
                        };
                        let lowered = ProgramExpression::Index(
                            Box::new(lowered.clone()),
                            Box::new(crate::surface::parser::flatten_array_indices(
                                indexes.clone(),
                                shape,
                            )),
                        );
                        Some(ContractExpression::ArrayIndex {
                            base: Box::new(field_expression),
                            indexes: indexes
                                .into_iter()
                                .map(ContractExpression::ProgramExpression)
                                .collect(),
                            dimensions: shape.to_vec(),
                            lowered,
                        })
                    } else {
                        Some(ContractExpression::Index(
                            Box::new(field_expression),
                            Box::new(ContractExpression::ProgramExpression(
                                ProgramExpression::Value(int32(index)),
                            )),
                        ))
                    }
                })
            })
        })
}

#[cfg(test)]
pub(super) fn bitvector_term_is_load_free(term: &MachineTerm) -> bool {
    pointer_indices::load_free(crate::kernel::MachineOperandView::Legacy(term))
}

fn synthesize_local_indexed_load(
    pointer: &Pointer,
    kind: crate::kernel::LoadKind,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let _frame = SurfaceSynthesisFrame::enter("local-index")?;
    state.locals().object_values().find_map(|(name, value)| {
        let view = value.pointer()?;
        let base = view.pointer();
        // `local[index]` is the C spelling only when the local is the base
        // the address was formed from: the address is the local's own offset
        // plus an index. Two unrelated pointers into one symbolic block (a
        // struct-pointer local and an array it points to, both external)
        // also have a numeric difference, but indexing the local by it names
        // a different C expression, one that reads the local as an `int32`
        // array and lowers to a different address term.
        if pointer.block != base.block
            || !(base.offset == PointerOffsetTerm::Constant(0)
                || matches!(&pointer.offset, PointerOffsetTerm::Add(left, right)
                    if left.as_ref() == &base.offset || right.as_ref() == &base.offset))
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
        Some(ContractExpression::Index(
            Box::new(ContractExpression::ProgramExpression(
                ProgramExpression::Variable(surface_local_name(name).to_string()),
            )),
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
    pointer: &Pointer,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    if !pointer.block.is_static_storage_block() {
        return None;
    }
    let owners = SYNTHESIS_STRUCT_OWNERS.with(|slot| slot.borrow().clone())?;
    state
        .locals()
        .array_objects_with_slot_in(&pointer.block)
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
                return Some(ContractExpression::Index(
                    Box::new(ContractExpression::ProgramExpression(base)),
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
            Some(ContractExpression::ArrayIndex {
                base: Box::new(ContractExpression::ProgramExpression(base)),
                indexes: indexes
                    .into_iter()
                    .map(ContractExpression::ProgramExpression)
                    .collect(),
                dimensions: shape.clone(),
                lowered,
            })
        })
}

fn synthesize_parameter_field_load(
    pointer: &Pointer,
    value_type: ProgramType,
    parameter_binding: ParameterBinding<'_>,
) -> Option<ContractExpression> {
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
        if field.interface_type().to_kernel_type() != value_type {
            continue;
        }
        let base = ProgramExpression::Variable(parameter.name().to_string());
        let field_pointer = if offset_bytes == 0 {
            base.clone()
        } else {
            ProgramExpression::PointerOffsetBytes {
                pointer: Box::new(base.clone()),
                bytes: offset_bytes,
            }
        };
        return Some(ContractExpression::Field {
            pointee_struct: None,
            base: Box::new(ContractExpression::ProgramExpression(base)),
            field: field_name.clone(),
            lowered: ProgramExpression::TypedLoad {
                pointer: Box::new(field_pointer),
                value_type,
                volatile: false,
                pointee_constant: field.pointee_is_constant(),
                access_class: None,
                source: Default::default(),
            },
            offset_bytes,
        });
    }
    None
}

/// The field read a struct-pointer local performs at `pointer`, spelled
/// `local->field`, when the installed local layout scope knows the local's
/// struct and this state holds the local's pointer value.
fn synthesize_local_field_load(
    pointer: &Pointer,
    value_type: ProgramType,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Option<ContractExpression> {
    for owner in struct_owners(parameter_binding, state) {
        // Compare each field's address with the load's pointer directly: an
        // object reached through an opaque `void *` keeps a byte-scaled
        // offset that element arithmetic over the struct width would miss.
        let Some((field_name, field)) = owner.layout.fields().iter().find(|(_, field)| {
            let field_pointer = owner.pointer.offset_by_bytes(field.offset_bytes());
            field_pointer.block == pointer.block
                && crate::kernel::offsets_have_same_canonical_form(
                    &field_pointer.offset,
                    &pointer.offset,
                )
        }) else {
            continue;
        };
        if field.interface_type().to_kernel_type() != value_type {
            continue;
        }
        return Some(ContractExpression::Field {
            pointee_struct: None,
            base: Box::new(ContractExpression::ProgramExpression(owner.base.clone())),
            field: field_name.clone(),
            lowered: ProgramExpression::TypedLoad {
                pointer: Box::new(owner_field_pointer(&owner.base, field.offset_bytes())),
                value_type,
                volatile: false,
                pointee_constant: field.pointee_is_constant(),
                access_class: None,
                source: Default::default(),
            },
            offset_bytes: field.offset_bytes(),
        });
    }
    None
}

/// A field read spelled through a struct-pointer parameter or, failing
/// that, through a struct-pointer local of the function under proof.
fn synthesize_struct_field_load(
    pointer: &Pointer,
    value_type: ProgramType,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Option<ContractExpression> {
    synthesize_parameter_field_load(pointer, value_type, parameter_binding)
        .or_else(|| synthesize_local_field_load(pointer, value_type, parameter_binding, state))
}

/// Recover source syntax for an opaque pointer value read from an owned
/// aggregate field. Offset-based synthesis cannot name its distinct block.
/// This is a candidate spelling; callers must re-lower it to the exact fact.
fn synthesize_owned_field_at_address(
    address: &Pointer,
    value_type: ProgramType,
    state: &ExecutionState,
) -> Option<ContractExpression> {
    let PointerBlock::Concrete(block) = &address.block else {
        return None;
    };
    let name = block.strip_prefix("local:")?.rsplit(':').next()?;
    let slot = state.locals().aggregate_object_pointer(name)?;
    let layout = state.locals().aggregate_layout(name)?;
    let field = layout.fields().iter().find(|field| {
        field.program_type() == value_type && slot.offset_by_bytes(field.offset_bytes()) == *address
    })?;
    let base = ProgramExpression::Variable(surface_local_name(name).to_string());
    Some(ContractExpression::Field {
        pointee_struct: None,
        base: Box::new(ContractExpression::ProgramExpression(base.clone())),
        field: field.name().to_string(),
        lowered: ProgramExpression::TypedLoad {
            pointer: Box::new(owner_field_pointer(&base, field.offset_bytes())),
            value_type,
            volatile: false,
            pointee_constant: false,
            access_class: None,
            source: Default::default(),
        },
        offset_bytes: field.offset_bytes(),
    })
}

/// The address of the pointer read that `pointer` is, when `state` names
/// that read: a legacy load variable whose canonical load in `state` is
/// itself, or a loaded pointer at displacement zero that `state`'s canonical
/// read of its defining address reproduces.
fn pointer_read_address_in_state(pointer: &Pointer, state: &ExecutionState) -> Option<Pointer> {
    if pointer.offset != PointerOffsetTerm::Constant(0) {
        return None;
    }
    let memory = crate::kernel::intern_memory_ref(state.memory());
    match &pointer.block {
        PointerBlock::Symbolic(variable) => {
            let (_, address) = crate::kernel::registered_load_for_variable(variable)?;
            registered_load_in_state(variable, state).map(|_| address)
        }
        PointerBlock::LoadedPointer(_) => {
            let read = pointer.as_loaded_value()?;
            // A retained read always names its exact defining snapshot,
            // including a post-store read whose canonical value is now known.
            (memory == read.defining_memory
                || Pointer::canonical_loaded_value(&memory, &read.defining_address) == *pointer)
                .then_some(read.defining_address)
        }
        _ => None,
    }
}

fn synthesize_owned_pointer_field(
    pointer: &Pointer,
    state: &ExecutionState,
) -> Option<ContractExpression> {
    let address = pointer_read_address_in_state(pointer, state)?;
    let PointerBlock::Concrete(block) = &address.block else {
        return None;
    };
    // Local storage names include a lifetime prefix when scopes reuse a name.
    // Look up the named object and verify its actual slot rather than scanning
    // all unrelated automatic aggregates in the snapshot.
    let name = block.strip_prefix("local:")?.rsplit(':').next()?;
    let slot = state.locals().aggregate_object_pointer(name)?;
    let layout = state.locals().aggregate_layout(name)?;
    let field = layout.fields().iter().find(|field| {
        field.program_type().is_pointer() && slot.offset_by_bytes(field.offset_bytes()) == address
    })?;
    let base = ProgramExpression::Variable(surface_local_name(name).to_string());
    Some(ContractExpression::Field {
        pointee_struct: None,
        base: Box::new(ContractExpression::ProgramExpression(base.clone())),
        field: field.name().to_string(),
        lowered: ProgramExpression::TypedLoad {
            pointer: Box::new(owner_field_pointer(&base, field.offset_bytes())),
            value_type: field.program_type(),
            volatile: false,
            pointee_constant: false,
            access_class: None,
            source: Default::default(),
        },
        offset_bytes: field.offset_bytes(),
    })
}

/// The element index `pointer` is at from `base`, as the term a source index
/// expression lowers to. A 64-bit index (`bytes[k]` for a `uint64` `k`) is
/// its own 64-bit value: spelled back, it lowers to the same displacement,
/// and every synthesized candidate is re-lowered and compared before use.
fn synthesis_element_index(
    pointer: &Pointer,
    base: &Pointer,
    element_width: u32,
) -> Option<pointer_indices::SourceIndex> {
    // Legacy-only offsets already have a native source reader. Retain that
    // result without importing temporary arithmetic. Any shared child selects
    // the shared path, so this compatibility read cannot export a shared DAG.
    let native = |offset: &PointerOffsetTerm| {
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
    if pointer.block != base.block {
        return None;
    }
    let displacement = match &pointer.offset {
        offset if base.offset == PointerOffsetTerm::Constant(0) => offset,
        PointerOffsetTerm::Add(left, right) if left.as_ref() == &base.offset => right.as_ref(),
        PointerOffsetTerm::Add(left, right) if right.as_ref() == &base.offset => left.as_ref(),
        _ => return None,
    };
    match displacement {
        PointerOffsetTerm::Int64Scaled {
            value,
            byte_width,
            unsigned,
        } if *byte_width == i64::from(element_width) => Some(pointer_indices::SourceIndex::Shared(
            pointer_indices::source_index(value, *unsigned),
        )),
        _ => None,
    }
}

fn synthesize_surface_pointer(
    pointer: &Pointer,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ProgramExpression> {
    let _pointer_frame =
        SurfacePointerFrame::enter(pointer, parameter_binding, state, bound_variables)?;
    let _frame = SurfaceSynthesisFrame::enter("pointer")?;
    if pointer == &Pointer::null() {
        return Some(ProgramExpression::Value(int32(0)));
    }
    // A function's address spells as the function's name.
    if let (PointerBlock::Function(function), PointerOffsetTerm::Constant(0)) =
        (&pointer.block, &pointer.offset)
    {
        return Some(ProgramExpression::FunctionAddress(function.clone()));
    }
    // A pointer a proof binder names, such as a match arm's payload.
    if let (PointerBlock::Symbolic(variable), PointerOffsetTerm::Constant(0)) =
        (&pointer.block, &pointer.offset)
        && let Some(name) =
            folds::binder_name(false, *variable).or_else(|| bound_variables.get(variable).cloned())
    {
        return Some(ProgramExpression::Variable(name.clone()));
    }
    // Exact parameter addresses retain their source identity at proof entry.
    // Naming a stored pointer must not enumerate all earlier parameters.
    if let Some((parameter, argument)) = parameter_binding
        .naming
        .and_then(|names| names.pointer_source(pointer))
        && parameter_names_its_argument(parameter.name(), argument, state)
    {
        return Some(ProgramExpression::Variable(parameter.name().to_string()));
    }
    if let Some(expression) = parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
        .find_map(|(parameter, argument)| {
            let ProgramExpression::Value(ProgramValue::Pointer(base)) = argument else {
                return None;
            };
            if !parameter_names_its_argument(parameter.name(), argument, state) {
                return None;
            }
            let element_width = parameter
                .interface_type()
                .pointee_type()?
                .to_kernel_type()
                .byte_width();
            let element_width = parameter
                .pointee_struct_layout()
                .or_else(|| parameter.struct_layout())
                .map_or(
                    element_width,
                    crate::languages::interface::RecordLayout::size_bytes,
                );
            let name = ProgramExpression::Variable(parameter.name().to_string());
            let Some(index) = synthesis_element_index(pointer, base, element_width) else {
                let bytes = pointer
                    .element_index_from_base_with_width(base, 1)?
                    .as_const()?;
                return (bytes <= i32::MAX as u32).then(|| ProgramExpression::PointerOffsetBytes {
                    pointer: Box::new(name),
                    bytes,
                });
            };
            let base = name;
            if pointer_indices::literal(index.operand_view()) == Some(MachineTerm::constant(0)) {
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
        .pointer_objects_in_block(&pointer.block)
        .find_map(|(name, base)| {
            crate::instrumentation::record_deterministic_work(1);
            let element_width = base.program_type().pointee_type()?.byte_width();
            let element_width = SYNTHESIS_STRUCT_OWNERS
                .with(|slot| {
                    slot.borrow()
                        .as_ref()
                        .and_then(|owners| owners.locals.get(name))
                        .map(crate::languages::interface::RecordLayout::size_bytes)
                })
                .unwrap_or(element_width);
            let name = ProgramExpression::Variable(surface_local_name(name).to_string());
            let Some(index) = synthesis_element_index(pointer, base, element_width) else {
                let bytes = pointer
                    .element_index_from_base_with_width(base, 1)?
                    .as_const()?;
                return (bytes <= i32::MAX as u32).then(|| ProgramExpression::PointerOffsetBytes {
                    pointer: Box::new(name),
                    bytes,
                });
            };
            let base = name;
            if pointer_indices::literal(index.operand_view()) == Some(MachineTerm::constant(0)) {
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
    if pointer.block.is_static_storage_block()
        && let PointerOffsetTerm::Constant(bytes) = pointer.offset
        && let Ok(bytes) = u32::try_from(bytes)
        && let Some(name) = state.locals().name_for_slot(&Pointer {
            block: pointer.block.clone(),
            offset: PointerOffsetTerm::Constant(0),
        })
        && (state.locals().aggregate_layout(name).is_some()
            || state.locals().scalar_object_type(name).is_some())
    {
        let base = ProgramExpression::AddressOf(Box::new(ProgramExpression::Variable(
            surface_local_name(name).to_string(),
        )));
        return Some(if bytes == 0 {
            base
        } else {
            ProgramExpression::PointerOffsetBytes {
                pointer: Box::new(base),
                bytes,
            }
        });
    }
    // A pointer into a global or static array, at a constant byte offset
    // from the array's slot: the array's name, displaced by those bytes.
    if pointer.block.is_static_storage_block()
        && let Some(expression) = state
            .locals()
            .array_objects_with_slot_in(&pointer.block)
            .into_iter()
            .find_map(|(name, _, slot)| {
                crate::instrumentation::record_deterministic_work(1);
                let (PointerOffsetTerm::Constant(at), PointerOffsetTerm::Constant(start)) =
                    (&pointer.offset, &slot.offset)
                else {
                    return None;
                };
                let bytes = u32::try_from(at.checked_sub(*start)?).ok()?;
                let base = ProgramExpression::Variable(surface_local_name(name).to_string());
                Some(if bytes == 0 {
                    base
                } else {
                    ProgramExpression::PointerOffsetBytes {
                        pointer: Box::new(base),
                        bytes,
                    }
                })
            })
    {
        return Some(expression);
    }
    if let (PointerBlock::Symbolic(variable), PointerOffsetTerm::Constant(0)) =
        (&pointer.block, &pointer.offset)
        && let Some(name) = proof_binder_name(*variable)
    {
        return Some(ProgramExpression::Variable(name));
    }
    if let Some(field) = synthesize_owned_pointer_field(pointer, state) {
        return contract_expression_to_program_expression(&field);
    }
    // A pointer read from a struct field spells as that field.
    if let Some(read) = pointer.as_loaded_value() {
        if let PointerOffsetTerm::Constant(bytes) = read.displacement
            && bytes != 0
        {
            let base = Pointer {
                block: pointer.block.clone(),
                offset: PointerOffsetTerm::Constant(0),
            };
            return Some(ProgramExpression::PointerOffsetBytes {
                pointer: Box::new(synthesize_surface_pointer(
                    &base,
                    parameter_binding,
                    state,
                    bound_variables,
                )?),
                bytes: u32::try_from(bytes).ok()?,
            });
        }
        if read.displacement != PointerOffsetTerm::Constant(0) {
            return None;
        }
        // A field spelling reads this state; historical reads need their
        // recorded selector before entering this C-only source fragment.
        pointer_read_address_in_state(pointer, state)?;
        let field = synthesize_struct_field_load(
            &read.defining_address,
            ProgramType::Int32Pointer,
            parameter_binding,
            state,
        )
        .or_else(|| {
            Some(ContractExpression::ProgramExpression(
                ProgramExpression::TypedLoad {
                    pointer: Box::new(synthesize_surface_pointer(
                        &read.defining_address,
                        parameter_binding,
                        state,
                        bound_variables,
                    )?),
                    value_type: ProgramType::Int32Pointer,
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
            ProgramExpression::Value(ProgramValue::Pointer(base)) if base.block == pointer.block
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
) -> Option<ContractExpression> {
    let (step, _) = state.step_results.as_ref()?.iter().find(|(_, value)| {
        crate::instrumentation::record_deterministic_work(1);
        matches(&value.native())
    })?;
    crate::surface::diagnostics::step_result_expression(*step)
}

fn synthesize_surface_pointer_expression(
    pointer: &Pointer,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let _frame = SurfaceSynthesisFrame::enter("pointer-expression")?;
    if let Some(region) = SYNTHESIS_RECORDED_POINTS
        .with(|points| points.borrow().as_ref()?.read_event_naming_pointer(pointer))
    {
        return Some(ContractExpression::RegionResult(region));
    }
    if let Some(region) = SYNTHESIS_RECORDED_POINTS
        .with(|points| points.borrow().as_ref()?.allocation_result(pointer))
    {
        return Some(ContractExpression::RegionAllocation(region));
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
        return Some(ContractExpression::At {
            selector,
            expression: Box::new(expression),
        });
    }
    if let Some(pointer) =
        synthesize_surface_pointer(pointer, parameter_binding, state, bound_variables)
    {
        return Some(ContractExpression::ProgramExpression(pointer));
    }
    if let Some(result) = state_call_result(
        state,
        |value| matches!(value, ProgramValue::Pointer(held) if held.pointer() == pointer),
    ) {
        return Some(result);
    }
    if parameter_binding.arguments.iter().any(|argument| {
        matches!(
            argument,
            ProgramExpression::Value(ProgramValue::Pointer(base)) if base.block == pointer.block
        )
    }) && let Some(offset) = synthesize_surface_pointer_offset(
        &pointer.offset,
        parameter_binding,
        state,
        bound_variables,
    ) {
        return Some(offset);
    }
    synthesize_snapshot_pointer_expression(pointer, parameter_binding, bound_variables)
        .or_else(|| {
            synthesize_entry_pointer_expression(pointer, parameter_binding, state, bound_variables)
        })
        .or_else(|| {
            synthesize_recorded_pointer_expression(pointer, parameter_binding, bound_variables)
        })
}

/// `at(point, e)` for a pointer no nearer state names, at a recorded point
/// where a local held a pointer into its block: the point that introduced
/// the value, found by the block in one index range.
fn synthesize_recorded_pointer_expression(
    pointer: &Pointer,
    parameter_binding: ParameterBinding<'_>,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let candidates = SYNTHESIS_RECORDED_POINTS.with(|slot| {
        let slot = slot.borrow();
        let points = slot.as_ref()?;
        Some(
            points
                .points_holding_pointer_block(&pointer.block)
                .map(|(selector, state)| (selector.clone(), state.clone()))
                .collect::<Vec<_>>(),
        )
    })?;
    candidates.into_iter().find_map(|(selector, state)| {
        let expression =
            synthesize_surface_pointer(pointer, parameter_binding, &state, bound_variables)?;
        Some(ContractExpression::At {
            selector,
            expression: Box::new(ContractExpression::ProgramExpression(expression)),
        })
    })
}

/// `old(e)` for a pointer the entry state names and this state does not.
/// The entry scope is cleared for the inner synthesis, so it never nests.
fn synthesize_entry_pointer_expression(
    pointer: &Pointer,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let _ = state;
    let entry = SYNTHESIS_ENTRY_STATE.with(|slot| slot.borrow().clone())?;
    let _cleared = SynthesisEntryScope(SYNTHESIS_ENTRY_STATE.with(|slot| slot.replace(None)));
    let expression =
        synthesize_surface_pointer_expression(pointer, parameter_binding, &entry, bound_variables)?;
    Some(ContractExpression::Old(Box::new(expression)))
}

/// A pointer value read from a struct field, whose block is the read itself
/// as a loaded pointer to a heap object is, spelled `local->field` where this
/// state, or failing that the snapshot state as `at(<selector>, ..)`,
/// registers that read.
fn synthesize_loaded_pointer_value(
    pointer: &crate::kernel::PointerValue,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Option<ContractExpression> {
    let at_state = |state: &ExecutionState| {
        let address = pointer_read_address_in_state(pointer.pointer(), state)?;
        synthesize_struct_field_load(&address, pointer.program_type(), parameter_binding, state)
    };
    at_state(state)
        .or_else(|| {
            let (snapshot, selector) =
                SYNTHESIS_SNAPSHOT_STATE.with(|slot| slot.borrow().clone())?;
            let expression = at_state(&snapshot)?;
            Some(ContractExpression::At {
                selector,
                expression: Box::new(expression),
            })
        })
        .or_else(|| {
            let (selector, recorded) = recorded_point_of_pointer_read(pointer.pointer(), state)?;
            Some(ContractExpression::At {
                selector,
                expression: Box::new(at_state(&recorded)?),
            })
        })
}

/// The recorded point whose memory holds the pointer read `pointer` is,
/// when `state` does not read it. The read is checked there with the
/// kernel's naming law, as [`pointer_read_address_in_state`] decides it.
fn recorded_point_of_pointer_read(
    pointer: &Pointer,
    state: &ExecutionState,
) -> Option<(SnapshotSelector, ExecutionState)> {
    if pointer.offset != PointerOffsetTerm::Constant(0) {
        return None;
    }
    let memory = match &pointer.block {
        PointerBlock::Symbolic(variable) => {
            crate::kernel::registered_load_for_variable(variable)?.0
        }
        PointerBlock::LoadedPointer(_) => pointer.as_loaded_value()?.defining_memory,
        _ => return None,
    };
    if pointer_read_address_in_state(pointer, state).is_some() {
        return None;
    }
    // Read where the memory is recorded or, for a memory no point records,
    // at a recorded memory near it that reads the same, as a load is.
    SYNTHESIS_RECORDED_POINTS.with(|slot| {
        let slot = slot.borrow();
        let points = slot.as_ref()?;
        points
            .point_reading_memory(&memory)
            .into_iter()
            .chain(points.points_near_memory(&memory))
            .find_map(|(selector, recorded)| {
                pointer_read_address_in_state(pointer, recorded)?;
                Some((selector.clone(), recorded.clone()))
            })
    })
}

/// The source spelling of a scalar model-field variable: `o.size` where the
/// current state's instance holds it at that field, `at(<selector>, o.size)`
/// where the snapshot state's does, and `old(o.size)` where the entry
/// state's does. One registry lookup and one instance lookup per state.
fn synthesize_scalar_model_field(
    variable: Variable,
    state: &ExecutionState,
) -> Option<ContractExpression> {
    let origin = crate::kernel::model_fields::registered_model_field_origin(variable)?;
    let owner = crate::kernel::model_fields::registered_instance_spelling(origin.identity)?;
    let field_at = |state: &ExecutionState| {
        let instance = state.resource_instance_at_path(origin.identity, &[])?;
        matches!(
            instance.fields().get(origin.field_index),
            Some(AlgebraicValue::Program(crate::kernel::integer_c_value!(MachineTerm::Variable(held)))) if *held == variable
        )
        .then_some(())?;
        // The field's declared C type, as the parser's elaboration records it.
        let crate::kernel::ResourceFieldType::Program(interface_type) =
            instance.schema().fields().get(origin.field_index)?.1
        else {
            return None;
        };
        Some(ContractExpression::ResourceField(ResourceFieldAccess {
            owner: owner.to_string(),
            resource_name: instance.name().to_string(),
            identity: origin.identity,
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
    if let Some(field) = SYNTHESIS_SNAPSHOT_STATE.with(|slot| {
        let slot = slot.borrow();
        let (snapshot, selector) = slot.as_ref()?;
        Some(ContractExpression::At {
            selector: selector.clone(),
            expression: Box::new(field_at(snapshot)?),
        })
    }) {
        return Some(field);
    }
    if let Some(field) = SYNTHESIS_ENTRY_STATE.with(|slot| {
        let slot = slot.borrow();
        Some(ContractExpression::Old(Box::new(field_at(slot.as_ref()?)?)))
    }) {
        return Some(field);
    }
    // The point whose instance first held this field value, in one lookup.
    SYNTHESIS_RECORDED_POINTS.with(|slot| {
        let slot = slot.borrow();
        let (selector, recorded) = slot.as_ref()?.point_holding_field_value(variable)?;
        Some(ContractExpression::At {
            selector: selector.clone(),
            expression: Box::new(field_at(recorded)?),
        })
    })
}

/// The `at(<selector>, e)` spelling of a pointer the current state cannot
/// name but the snapshot state can, such as a call's `old(p->kid)` read at
/// that call's entry. The snapshot scope is cleared for the inner synthesis,
/// so the snapshot spelling never nests.
fn synthesize_snapshot_pointer_expression(
    pointer: &Pointer,
    parameter_binding: ParameterBinding<'_>,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let (snapshot, selector) = SYNTHESIS_SNAPSHOT_STATE.with(|slot| slot.borrow().clone())?;
    let _cleared = SynthesisSnapshotScope(SYNTHESIS_SNAPSHOT_STATE.with(|slot| slot.replace(None)));
    let expression = synthesize_surface_pointer_expression(
        pointer,
        parameter_binding,
        &snapshot,
        bound_variables,
    )?;
    Some(ContractExpression::At {
        selector,
        expression: Box::new(expression),
    })
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
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let _frame = SurfaceSynthesisFrame::enter("algebraic")?;
    if let crate::kernel::AlgebraicTermNode::Variable(variable) = &term.node
        && let Some(name) = folds::scoped_binder_name(folds::BinderCarrier::Algebraic, *variable)
    {
        return Some(SurfaceTerm::Binding(name));
    }
    match &term.node {
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
            Some(ContractExpression::Binding(name.clone()))
        }
        crate::kernel::AlgebraicTermNode::PureFunctionApplication { name, arguments } => {
            synthesize_surface_call(name, arguments, parameter_binding, state, bound_variables)
        }
        crate::kernel::AlgebraicTermNode::Variable(variable) => {
            if let Some(name) = proof_binder_name(*variable) {
                return Some(ContractExpression::Binding(name));
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
                return Some(ContractExpression::ProgramExpression(
                    ProgramExpression::Variable(parameter.name().to_string()),
                ));
            }
            // A value a call returned is spelled by its call.
            if let Some(result) = state_call_result(
                state,
                |value| matches!(value, ProgramValue::Parameter(held) if held.as_ref() == term),
            ) {
                return if matches!(result, ContractExpression::RegionResult(_)) {
                    typed_algebraic_result(&term.algebraic_type, result)
                } else {
                    Some(result)
                };
            }
            if let Some(region) = SYNTHESIS_RECORDED_POINTS
                .with(|slot| slot.borrow().as_ref()?.call_result_naming_algebraic(term))
            {
                return typed_algebraic_result(
                    &term.algebraic_type,
                    ContractExpression::RegionResult(region),
                );
            }
            // A value a local holds, a Rust local of an enum, a `Vec` or a
            // library iterator, is spelled by that local: now, or at the
            // snapshot the goal reads.
            let held_by = |state: &ExecutionState| {
                state
                    .locals()
                    .names_holding_algebraic(term)
                    .first()
                    .map(|name| {
                        ContractExpression::ProgramExpression(ProgramExpression::Variable(
                            surface_local_name(name).to_string(),
                        ))
                    })
            };
            if let Some(local) = held_by(state) {
                return Some(local);
            }
            if let Some(local) = SYNTHESIS_SNAPSHOT_STATE.with(|slot| {
                let slot = slot.borrow();
                let (state, selector) = slot.as_ref()?;
                Some(ContractExpression::At {
                    selector: selector.clone(),
                    expression: Box::new(held_by(state)?),
                })
            }) {
                return Some(local);
            }
            let origin = crate::kernel::model_fields::registered_model_field_origin(*variable)?;
            let owner = crate::kernel::model_fields::registered_instance_spelling(origin.identity)?;
            let field_at = |state: &ExecutionState| {
                let instance = state.resource_instance_at_path(origin.identity, &[])?;
                let held = instance.fields().get(origin.field_index)?;
                let exact = match held {
                    crate::kernel::AlgebraicValue::Algebraic(value) => value == term,
                    crate::kernel::AlgebraicValue::Program(ProgramValue::Parameter(value)) => {
                        value.as_ref() == term
                    }
                    _ => false,
                };
                exact.then_some(())?;
                Some(ContractExpression::ResourceField(ResourceFieldAccess {
                    owner: owner.to_string(),
                    resource_name: instance.name().to_string(),
                    identity: origin.identity,
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
                Some(ContractExpression::Old(Box::new(field_at(
                    slot.borrow().as_ref()?,
                )?)))
            }) {
                return Some(field);
            }
            SYNTHESIS_RECORDED_POINTS.with(|slot| {
                let points = slot.borrow();
                let (selector, recorded) = points.as_ref()?.point_holding_field_value(*variable)?;
                Some(ContractExpression::At {
                    selector: selector.clone(),
                    expression: Box::new(field_at(recorded)?),
                })
            })
        }

        // The value a reference parameter refers to is spelled `*r`.
        crate::kernel::AlgebraicTermNode::MemoryLoad { pointer, .. } => parameter_binding
            .parameters
            .iter()
            .zip(parameter_binding.arguments)
            .find(|(_, argument)| {
                matches!(argument, ProgramExpression::Value(ProgramValue::Pointer(value))
                    if value.pointer() == pointer.as_ref())
            })
            .map(|(parameter, _)| {
                ContractExpression::ProgramExpression(ProgramExpression::Load(Box::new(
                    ProgramExpression::Variable(parameter.name().to_string()),
                )))
            })
            .or_else(|| synthesize_held_value_local(term, pointer, state))
            .or_else(|| synthesize_recorded_held_value_local(term, pointer)),
        crate::kernel::AlgebraicTermNode::Constructor { variant, fields } => {
            let arguments = fields
                .iter()
                .map(|field| match field {
                    crate::kernel::AlgebraicValue::Program(ProgramValue::Parameter(term)) => {
                        synthesize_surface_algebraic(
                            term,
                            parameter_binding,
                            state,
                            bound_variables,
                        )
                    }
                    crate::kernel::AlgebraicValue::Algebraic(term) => synthesize_surface_algebraic(
                        term,
                        parameter_binding,
                        state,
                        bound_variables,
                    ),
                    crate::kernel::AlgebraicValue::Program(ProgramValue::Pointer(pointer)) => {
                        synthesize_surface_pointer_expression(
                            pointer,
                            parameter_binding,
                            state,
                            bound_variables,
                        )
                        .or_else(|| {
                            synthesize_loaded_pointer_value(pointer, parameter_binding, state)
                        })
                        .map(|expression| {
                            // Constructors implicitly retag object pointers
                            // without widening their views. An explicit cast
                            // is needed only for a checked root view; adding
                            // it to a saved narrow view would change the value.
                            if pointer.program_type() == ProgramType::VoidPointer
                                && pointer.extent_is_known()
                                && pointer.extent().is_none()
                            {
                                ContractExpression::CUnary {
                                    lowered: ProgramExpression::Cast {
                                        expression: Box::new(ProgramExpression::Value(
                                            ProgramValue::Pointer(pointer.clone()),
                                        )),
                                        target_type: ProgramType::VoidPointer,
                                        integer_mode: crate::kernel::IntegerCastMode::Standard,
                                        pointee_struct: None,
                                        pointee_volatile: false,
                                        pointee_constant: false,
                                        explicit_qualification: false,
                                    },
                                    operand: Box::new(expression),
                                }
                            } else {
                                expression
                            }
                        })
                    }
                    crate::kernel::AlgebraicValue::Program(ProgramValue::Int32(value)) => {
                        synthesize_surface_bitvector(
                            value,
                            parameter_binding,
                            state,
                            bound_variables,
                        )
                    }
                    // A field of another scalar width that a binder names is
                    // spelled by that binder, which carries its own type;
                    // otherwise by the local, parameter or `result` holding
                    // it, which carry theirs. A constant of such a width
                    // would need its literal suffix and is not spelled.
                    crate::kernel::AlgebraicValue::Program(
                        ProgramValue::Bool(value @ MachineTerm::Variable(variable))
                        | ProgramValue::Int8(value @ MachineTerm::Variable(variable))
                        | ProgramValue::Int16(value @ MachineTerm::Variable(variable))
                        | ProgramValue::UInt8(value @ MachineTerm::Variable(variable))
                        | ProgramValue::UInt16(value @ MachineTerm::Variable(variable))
                        | ProgramValue::UInt32(value @ MachineTerm::Variable(variable))
                        | ProgramValue::Int64(value @ MachineTerm::Variable(variable))
                        | ProgramValue::UInt64(value @ MachineTerm::Variable(variable)),
                    ) => bound_variables
                        .get(variable)
                        .map(|name| {
                            ContractExpression::ProgramExpression(ProgramExpression::Variable(
                                name.clone(),
                            ))
                        })
                        .or_else(|| {
                            synthesize_surface_bitvector(
                                value,
                                parameter_binding,
                                state,
                                bound_variables,
                            )
                        }),
                    _ => None,
                })
                .collect::<Option<Vec<_>>>()?;
            Some(ContractExpression::AlgebraicConstructor {
                algebraic_type: surface_algebraic_type(&term.algebraic_type)?,
                variant: variant.clone(),
                arguments,
            })
        }
        _ => None,
    }
}

/// A recorded call result has a type in the kernel, but no lexical binding
/// from which Surface's generic/method resolution can recover it. Keep that
/// type in a local expression binder. Its body is only the new binding, so
/// its name cannot capture any source expression.
fn typed_algebraic_result(
    ty: &crate::kernel::AlgebraicType,
    value: ContractExpression,
) -> Option<ContractExpression> {
    Some(ContractExpression::Let {
        name: "__click_result".into(),
        click_type: Some(ClickType::Algebraic(surface_algebraic_type(ty)?)),
        value: Box::new(value),
        body: Box::new(ContractExpression::Binding("__click_result".into())),
    })
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
