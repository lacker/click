//! Raising the values of the built-in slice type
//! (`design/rust-slice-values.md`, step 2b-iii-c-ii). A slice raises as the
//! one value that names it where one does: a binder or parameter (`s`), a
//! slice-valued pure application (`f(x)`) or a read of a slice cell; any
//! other slice as its construction, `slice::from_raw_parts(p, n)`. Its
//! components raise as `s.len()` and `s.as_ptr()` of the slice that names
//! them. Each spelling lowers back to the same kernel term: the name to the
//! value it names, `len` and `as_ptr` to the components read in place, and
//! `from_raw_parts` to the wide pointer it builds.
//!
//! A string slice, `Str`, is the same wide pointer at its own type
//! (`design/rust-slice-values.md`, "String slices"). Its components raise
//! as `str::len(s)` and `str::as_ptr(s)`, and a slice whose type is not its
//! name's is that name retyped: `str::as_bytes(s)` for the bytes of a
//! string slice `s`, `str::from_utf8_unchecked(v)` for the string slice of
//! a byte slice `v`, as an unnamed string slice is of its construction.
//! Each lowers to the cast between slice types it was built by.

use super::*;

fn slice_call(name: &str, arguments: Vec<SyntaxTerm>) -> SyntaxTerm {
    SyntaxTerm::Call {
        name: name.to_string(),
        arguments,
    }
}

/// The wide pointer `slice` as Surface.
pub(super) fn raise_slice(
    slice: &crate::kernel::Pointer,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let count = slice.len()?;
    let thin = slice.as_ptr();
    let string =
        slice.program_type() == ProgramType::SlicePointer(crate::kernel::SliceElement::Str);
    if let Some(Named {
        slice: named,
        string: named_string,
    }) = named_slice(
        thin.address(),
        count,
        slice.program_type(),
        parameter_binding,
        state,
        bound_variables,
    ) {
        return Some(retyped(named, named_string, string));
    }
    let data = raise_slice_data(thin.address(), parameter_binding, state, bound_variables)?;
    let count = synthesize_surface_bitvector(count, parameter_binding, state, bound_variables)?;
    Some(retyped(
        slice_call(crate::surface::RUST_SLICE_FROM_RAW_PARTS, vec![data, count]),
        false,
        string,
    ))
}

/// A value that names a slice, and whether its own type is the string
/// slice `Str`.
struct Named {
    slice: SyntaxTerm,
    string: bool,
}

/// `named`, a slice whose own type is `Str` when `named_string` holds, at
/// the type of a string slice when `string` holds and of a byte slice
/// otherwise: itself at its own type, else retyped by `str::as_bytes` or
/// `str::from_utf8_unchecked`, the casts between the two.
fn retyped(named: SyntaxTerm, named_string: bool, string: bool) -> SyntaxTerm {
    match (named_string, string) {
        (true, false) => slice_call(crate::surface::RUST_STR_AS_BYTES, vec![named]),
        (false, true) => slice_call(crate::surface::RUST_STR_FROM_UTF8_UNCHECKED, vec![named]),
        _ => named,
    }
}

/// Whether the slice the variable `variable` names is a string slice: the
/// type its proof binder or its parameter declares. A slice a Rust call
/// returns is named by [`call_result_slice`], which gives its element.
fn slice_variable_is_string(variable: Variable, parameter_binding: ParameterBinding<'_>) -> bool {
    let element = folds::slice_binder_element(variable).or_else(|| {
        match slice_parameter_of(variable, parameter_binding)?.interface_type() {
            crate::languages::interface::InterfaceType::Slice(element) => Some(element),
            _ => None,
        }
    });
    element == Some(crate::kernel::SliceElement::Str)
}

/// Whether the pure function `name` returns a string slice.
fn application_is_string(name: &str) -> bool {
    crate::surface::diagnostics::slice_result_element(name)
        == Some(crate::kernel::SliceElement::Str)
}

/// The slice whose undisplaced data pointer is `address` and whose count is
/// `count`, when one value names both: a slice named by a variable, a
/// slice-valued pure application, or a read of a slice cell, read at
/// `slice_type`.
fn named_slice(
    address: &Address,
    count: &OldMachineTerm,
    slice_type: ProgramType,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<Named> {
    // A Rust `fn`'s slice parameter is its argument, whose data pointer is
    // the external argument a thin parameter would have
    // (`design/rust-slice-values.md`, step 3b).
    if let Some(parameter) = slice_parameter_with(address, count, parameter_binding) {
        return Some(Named {
            slice: parameter_slice(parameter),
            string: parameter.interface_type()
                == crate::languages::interface::InterfaceType::Slice(
                    crate::kernel::SliceElement::Str,
                ),
        });
    }
    if !matches!(address.offset.view(), OffsetView::Constant(0)) {
        return None;
    }
    match (&address.base, count) {
        (AddressBase::Symbolic(variable), OldMachineTerm::Variable(counted))
            if counted.counted_slice() == Some(*variable)
                && let Some((slice, element)) = call_result_slice(address, state) =>
        {
            Some(Named {
                slice,
                string: element == crate::kernel::SliceElement::Str,
            })
        }
        (AddressBase::Symbolic(variable), OldMachineTerm::Variable(counted))
            if counted.counted_slice() == Some(*variable) =>
        {
            Some(Named {
                slice: slice_variable(*variable, parameter_binding, state, bound_variables)?,
                string: slice_variable_is_string(*variable, parameter_binding),
            })
        }
        (
            AddressBase::PureFunctionApplication(application),
            OldMachineTerm::PureApplicationCount(counted),
        ) if application == counted && !application.name().starts_with('$') => Some(Named {
            slice: synthesize_surface_call(
                application.name(),
                application.arguments(),
                parameter_binding,
                state,
                bound_variables,
            )?,
            string: application_is_string(application.name()),
        }),
        // A read names the slice at the type its cell declares; the same
        // read at another slice type names nothing and raises as its
        // construction from `str::as_ptr` and `str::len` of the read.
        (
            AddressBase::SliceData(load),
            OldMachineTerm::MemoryLoad(_, read, crate::kernel::LoadKind::SliceCount),
        ) if read.load() == load => Some(Named {
            slice: slice_read(load, slice_type, parameter_binding, state, bound_variables)?,
            string: slice_type == ProgramType::SlicePointer(crate::kernel::SliceElement::Str),
        }),
        _ => None,
    }
}

/// The slice the variable `variable` names (`design/rust-slice-values.md`,
/// step 2b-iii-a): a proof binder's name, or the parameter whose argument is
/// that slice.
fn slice_variable(
    variable: Variable,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    if let Some(name) =
        folds::binder_name(false, variable).or_else(|| bound_variables.get(&variable).cloned())
    {
        return Some(SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
            name.into(),
        )));
    }
    if let Some(parameter) = slice_parameter_of(variable, parameter_binding) {
        return Some(SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
            crate::surface::surface_parameter_binding(parameter.binding_name()),
        )));
    }
    // A slice a Rust call returned is the call's result.
    if let Some((slice, _)) = call_result_slice(&Address::symbolic(variable), state) {
        return Some(slice);
    }
    // A slice local that holds this slice, here or at a recorded point,
    // such as a slice iterator's slice at a loop's head
    // (`design/rust-slice-values.md`, step 4b). A thin local holding its
    // data pointer names the data pointer, never the slice.
    if let Some((local, _)) = program_slice_local(variable, state, |slice| slice) {
        return Some(local);
    }
    // Another value named where it was introduced is named by its
    // address's routes.
    synthesize_surface_pointer_expression(
        &Address::symbolic(variable),
        parameter_binding,
        state,
        bound_variables,
    )
}

/// `component` of the slice local that holds the slice the variable
/// `variable` names: in `state`, the local itself, or `at(p, local)` at
/// the first recorded point whose state holds it.
fn program_slice_local(
    variable: Variable,
    state: &ExecutionState,
    component: impl Fn(ProgramExpression) -> ProgramExpression,
) -> Option<(SyntaxTerm, crate::kernel::SliceElement)> {
    if let Some((local, element)) = slice_local_holding(variable, state) {
        return Some((SyntaxTerm::ProgramExpression(component(local)), element));
    }
    let base = AddressBase::Symbolic(variable);
    SYNTHESIS_RECORDED_POINTS.with(|slot| {
        let slot = slot.borrow();
        slot.as_ref()?
            .points_holding_address_base(&base)
            .find_map(|(selector, recorded)| {
                let (local, element) = slice_local_holding(variable, recorded)?;
                Some((
                    SyntaxTerm::At {
                        selector: selector.clone(),
                        expression: Box::new(SyntaxTerm::ProgramExpression(component(local))),
                    },
                    element,
                ))
            })
    })
}

/// The count of the slice the variable `variable` names, as the program's
/// own component read `local.len()` of the slice local that holds it, here
/// or at a recorded point.
fn program_slice_local_count(variable: Variable, state: &ExecutionState) -> Option<SyntaxTerm> {
    program_slice_local(variable, state, |slice| {
        ProgramExpression::SliceLength(Box::new(slice))
    })
    .map(|(count, _)| count)
}

/// The local of `state` that holds the slice the variable `variable` names,
/// its data pointer and count: its name, with the slice's element. One
/// lookup in the index of locals holding a pointer into the slice's block.
fn slice_local_holding(
    variable: Variable,
    state: &ExecutionState,
) -> Option<(ProgramExpression, crate::kernel::SliceElement)> {
    let count = OldMachineTerm::Variable(variable.element_count());
    state
        .locals()
        .pointer_objects_in_block(&AddressBase::Symbolic(variable))
        .find_map(|(name, held)| {
            crate::instrumentation::record_deterministic_work(1);
            let ProgramType::SlicePointer(element) = held.program_type() else {
                return None;
            };
            (held.is_wide()
                && held.len() == Some(&count)
                && matches!(held.address().offset.view(), OffsetView::Constant(0))
                && has_surface_iterator_binding(name))
            .then(|| {
                (
                    ProgramExpression::Variable(crate::kernel::program_local_source_name(name)),
                    element,
                )
            })
        })
}

/// The slice parameter `parameter` as Surface: its name.
fn parameter_slice(parameter: &crate::languages::interface::ImportedParameter) -> SyntaxTerm {
    SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
        crate::surface::surface_parameter_binding(parameter.binding_name()),
    ))
}

/// The parameter whose argument is the slice with data pointer `address`
/// and count `count`.
fn slice_parameter_with<'a>(
    address: &Address,
    count: &OldMachineTerm,
    parameter_binding: ParameterBinding<'a>,
) -> Option<&'a crate::languages::interface::ImportedParameter> {
    parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
        .find_map(|(parameter, argument)| {
            crate::instrumentation::record_deterministic_work(1);
            let ProgramExpression::Value(ProgramValue::Pointer(value)) = argument else {
                return None;
            };
            (value.len() == Some(count) && value.address() == address).then_some(parameter)
        })
}

/// The slice parameter whose argument's count is `count`.
fn slice_parameter_counted<'a>(
    count: &OldMachineTerm,
    parameter_binding: ParameterBinding<'a>,
) -> Option<&'a crate::languages::interface::ImportedParameter> {
    parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
        .find_map(|(parameter, argument)| {
            crate::instrumentation::record_deterministic_work(1);
            let ProgramExpression::Value(ProgramValue::Pointer(value)) = argument else {
                return None;
            };
            (value.len() == Some(count)).then_some(parameter)
        })
}

/// The slice parameter whose argument's data pointer is the base of
/// `address`, displaced by whole elements of its slice.
fn slice_parameter_data<'a>(
    address: &Address,
    parameter_binding: ParameterBinding<'a>,
) -> Option<(
    &'a crate::languages::interface::ImportedParameter,
    pointer_indices::SourceIndex,
)> {
    parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
        .find_map(|(parameter, argument)| {
            crate::instrumentation::record_deterministic_work(1);
            let ProgramExpression::Value(ProgramValue::Pointer(value)) = argument else {
                return None;
            };
            let crate::languages::interface::InterfaceType::Slice(element) =
                parameter.interface_type()
            else {
                return None;
            };
            if !value.is_wide() || value.address().base != address.base {
                return None;
            }
            let width = element.thin_pointer_type().pointee_type()?.byte_width();
            Some((
                parameter,
                synthesis_element_index(address, value.address(), width)?,
            ))
        })
}

/// The slice a Rust call returned whose data pointer is `data`, with its
/// element (`design/rust-slice-values.md`, step 3c-i): the call's result as
/// the program names it, a live call step or a recorded call's region
/// result. Only a wide result names it: a thin result at the same address
/// is no slice.
fn call_result_slice(
    data: &Address,
    state: &ExecutionState,
) -> Option<(SyntaxTerm, crate::kernel::SliceElement)> {
    if !matches!(data.base, AddressBase::Symbolic(_))
        || !matches!(data.offset.view(), OffsetView::Constant(0))
    {
        return None;
    }
    let element = |held: &crate::kernel::Pointer| match held.program_type() {
        ProgramType::SlicePointer(element) => Some(element),
        _ => None,
    };
    if let Some((step, found)) = state.step_results.as_ref().and_then(|results| {
        results.iter().find_map(|(step, value)| {
            crate::instrumentation::record_deterministic_work(1);
            match &*value.native() {
                ProgramValue::Pointer(held) if held.is_wide() && held.address() == data => {
                    Some((*step, element(&held)?))
                }
                _ => None,
            }
        })
    }) && let Some(result) = crate::surface::diagnostics::step_result_expression(step)
    {
        return Some((result, found));
    }
    SYNTHESIS_RECORDED_POINTS.with(|points| {
        let points = points.borrow();
        let (region, held) = points.as_ref()?.call_result_naming_slice(data)?;
        Some((SyntaxTerm::RegionResult(region), element(&held)?))
    })
}

/// The parameter whose argument is the slice `variable` names.
fn slice_parameter_of<'a>(
    variable: Variable,
    parameter_binding: ParameterBinding<'a>,
) -> Option<&'a crate::languages::interface::ImportedParameter> {
    parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
        .find_map(|(parameter, argument)| {
            crate::instrumentation::record_deterministic_work(1);
            let ProgramExpression::Value(ProgramValue::Pointer(value)) = argument else {
                return None;
            };
            (value.is_wide()
                && value.address().base == AddressBase::Symbolic(variable)
                && matches!(value.address().offset.view(), OffsetView::Constant(0)))
            .then_some(parameter)
        })
}

/// The slice stored in a slice cell, read where `load` reads it, at
/// `slice_type`: the read of that place.
fn slice_read(
    load: &crate::kernel::Load,
    slice_type: ProgramType,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    synthesize_point_read(
        load.point(),
        load.cell(),
        slice_type,
        parameter_binding,
        state,
        bound_variables,
    )
}

/// The count of a slice, `count`, as `s.len()` of the slice that names it:
/// a variable's slice, a slice-valued application, or a slice cell's read;
/// `str::len(s)` when that slice is a string slice. `None` for a term that
/// is no slice's own count.
pub(super) fn raise_slice_count(
    count: &OldMachineTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let (slice, string) = match count {
        // A Rust `fn`'s slice parameter's count.
        _ if let Some(parameter) = slice_parameter_counted(count, parameter_binding) => (
            parameter_slice(parameter),
            parameter.interface_type()
                == crate::languages::interface::InterfaceType::Slice(
                    crate::kernel::SliceElement::Str,
                ),
        ),
        OldMachineTerm::Variable(counted)
            if let Some((slice, element)) =
                call_result_slice(&Address::symbolic(counted.counted_slice()?), state) =>
        {
            (slice, element == crate::kernel::SliceElement::Str)
        }
        OldMachineTerm::Variable(counted)
            // A slice no binder or parameter names, which a slice local
            // holds: the program's own `local.len()`, as `slice_variable`
            // names the slice.
            if let Some(local) = counted
                .counted_slice()
                .filter(|variable| {
                    folds::binder_name(false, *variable).is_none()
                        && !bound_variables.contains_key(variable)
                        && slice_parameter_of(*variable, parameter_binding).is_none()
                })
                .and_then(|variable| program_slice_local_count(variable, state)) =>
        {
            return Some(local);
        }
        OldMachineTerm::Variable(counted) => {
            let variable = counted.counted_slice()?;
            (
                slice_variable(variable, parameter_binding, state, bound_variables)?,
                slice_variable_is_string(variable, parameter_binding),
            )
        }
        OldMachineTerm::PureApplicationCount(application)
            if !application.name().starts_with('$') =>
        {
            (
                synthesize_surface_call(
                    application.name(),
                    application.arguments(),
                    parameter_binding,
                    state,
                    bound_variables,
                )?,
                application_is_string(application.name()),
            )
        }
        // The count does not fix the element type; the cell's declaration
        // does, as for a pointer load nested in an address
        // (`design/loads.md`, "Raising").
        OldMachineTerm::MemoryLoad(_, read, crate::kernel::LoadKind::SliceCount) => {
            let read = slice_read(
                read.load(),
                ProgramType::Pointer,
                parameter_binding,
                state,
                bound_variables,
            )?;
            let string = spelled_load_type(&read)
                == Some(ProgramType::SlicePointer(crate::kernel::SliceElement::Str));
            (read, string)
        }
        _ => return None,
    };
    let len = if string {
        crate::surface::RUST_STR_LEN
    } else {
        crate::surface::RUST_SLICE_LEN
    };
    Some(slice_call(len, vec![slice]))
}

/// A slice's data pointer, `address`, as `s.as_ptr()` of the slice that
/// names it, displaced by its element index, where a slice names its base;
/// any other thin pointer by its address's routes.
pub(super) fn raise_slice_data(
    address: &Address,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    slice_data_pointer(address, parameter_binding, state, bound_variables).or_else(|| {
        synthesize_surface_pointer_expression(address, parameter_binding, state, bound_variables)
    })
}

/// The thin pointer `address` as `s.as_ptr()`, or `s.as_ptr() + k`, when
/// its base is the data pointer of a slice `s` that names it: a slice read,
/// a slice-valued pure call, a slice binder or a slice parameter. `None` for
/// any other base.
pub(super) fn slice_data_pointer(
    address: &Address,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    // A Rust `fn`'s slice parameter's data pointer, displaced by `k`
    // elements: `bytes.as_ptr() + k`.
    if address.base == AddressBase::ExternalArgument
        && let Some((parameter, index)) = slice_parameter_data(address, parameter_binding)
    {
        // The program's own component read, `bytes.as_ptr()`, which lowers
        // to the data pointer of the parameter's value and is a C
        // expression a range or an index is written on.
        let data = SyntaxTerm::ProgramExpression(ProgramExpression::SliceData(Box::new(
            ProgramExpression::Variable(crate::surface::surface_parameter_binding(
                parameter.binding_name(),
            )),
        )));
        if pointer_indices::literal(index.operand_view()) == Some(OldMachineTerm::constant(0)) {
            return Some(data);
        }
        let index = pointer_indices::raise(
            index.operand_view(),
            parameter_binding,
            state,
            bound_variables,
        )?;
        return Some(SyntaxTerm::Add(Box::new(data), Box::new(index)));
    }
    // The data pointer of a slice no binder or parameter names, which a
    // slice local holds, here or at a recorded point, displaced by `k`
    // elements: the program's own `local.as_ptr() + k`
    // (`design/rust-slice-values.md`, step 4b).
    if let AddressBase::Symbolic(variable) = &address.base
        && folds::binder_name(false, *variable).is_none()
        && !bound_variables.contains_key(variable)
        && slice_parameter_of(*variable, parameter_binding).is_none()
        && call_result_slice(&Address::symbolic(*variable), state).is_none()
        && let Some((data, element)) = program_slice_local(*variable, state, |slice| {
            ProgramExpression::SliceData(Box::new(slice))
        })
    {
        let width = element.thin_pointer_type().pointee_type()?.byte_width();
        let origin = address.with_offset(crate::kernel::AddressOffset::constant(0));
        let index = synthesis_element_index(address, &origin, width)?;
        if pointer_indices::literal(index.operand_view()) == Some(OldMachineTerm::constant(0)) {
            return Some(data);
        }
        let index = pointer_indices::raise(
            index.operand_view(),
            parameter_binding,
            state,
            bound_variables,
        )?;
        return Some(SyntaxTerm::Add(Box::new(data), Box::new(index)));
    }
    let (slice, element) = match &address.base {
        AddressBase::SliceData(load) => {
            let read = slice_read(
                load,
                ProgramType::Pointer,
                parameter_binding,
                state,
                bound_variables,
            )?;
            let ProgramType::SlicePointer(element) = spelled_load_type(&read)? else {
                return None;
            };
            (read, element)
        }
        // A slice-valued pure call is the slice; its data pointer is based
        // on the application (`design/rust-slice-values.md`, step
        // 2b-iii-b-ii).
        AddressBase::PureFunctionApplication(application)
            if !application.name().starts_with('$') =>
        {
            let element = crate::surface::diagnostics::slice_result_element(application.name())?;
            (
                synthesize_surface_call(
                    application.name(),
                    application.arguments(),
                    parameter_binding,
                    state,
                    bound_variables,
                )?,
                element,
            )
        }
        // A slice a Rust call returned.
        AddressBase::Symbolic(_)
            if let Some(found) = call_result_slice(
                &address.with_offset(crate::kernel::AddressOffset::constant(0)),
                state,
            ) =>
        {
            found
        }
        // A match arm's slice binder.
        AddressBase::Symbolic(variable)
            if let Some(element) = folds::slice_binder_element(*variable)
                && let Some(name) = folds::binder_name(false, *variable) =>
        {
            (
                SyntaxTerm::ProgramExpression(ProgramExpression::Variable(name.into())),
                element,
            )
        }
        AddressBase::Symbolic(variable) => {
            let parameter = slice_parameter_of(*variable, parameter_binding)?;
            let crate::languages::interface::InterfaceType::Slice(element) =
                parameter.interface_type()
            else {
                return None;
            };
            (
                SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                    crate::surface::surface_parameter_binding(parameter.binding_name()),
                )),
                element,
            )
        }
        _ => return None,
    };
    // A string slice's data pointer is `str::as_ptr(s)`, a `u8` pointer.
    let as_ptr = if element == crate::kernel::SliceElement::Str {
        crate::surface::RUST_STR_AS_PTR
    } else {
        crate::surface::RUST_SLICE_AS_PTR
    };
    let element_width = element.thin_pointer_type().pointee_type()?.byte_width();
    let data = slice_call(as_ptr, vec![slice]);
    let origin = address.with_offset(crate::kernel::AddressOffset::constant(0));
    let index = synthesis_element_index(address, &origin, element_width)?;
    if pointer_indices::literal(index.operand_view()) == Some(OldMachineTerm::constant(0)) {
        return Some(data);
    }
    let index = pointer_indices::raise(
        index.operand_view(),
        parameter_binding,
        state,
        bound_variables,
    )?;
    Some(SyntaxTerm::Add(Box::new(data), Box::new(index)))
}

/// A program slice operation (`design/rust-slice-values.md`, step 3) as
/// Surface over its operands, which stay program expressions: `s.len()` and
/// `s.as_ptr()` as methods of the operand, resolved by its type as a byte or
/// a string slice's are, and `slice::from_raw_parts(p, n)`. Each lowers to
/// the spec operation the program operation evaluates as. A construction is
/// never spelled `s[a..b]`: that spelling lowers to a construction that owes
/// the subslice's bounds, which a program construction does not, so only a
/// construction the kernel recorded under its bounds is spelled so. `None`
/// for any other expression.
pub(in crate::surface) fn raise_program_slice_operation(
    expression: &ProgramExpression,
) -> Option<SyntaxTerm> {
    let operand = |operand: &ProgramExpression| SyntaxTerm::ProgramExpression(operand.clone());
    let method = |slice: &ProgramExpression, method: &str| SyntaxTerm::MethodCall {
        receiver: Box::new(operand(slice)),
        method: method.to_string(),
        arguments: Vec::new(),
    };
    Some(match expression {
        ProgramExpression::SliceLength(slice) => method(slice, "len"),
        ProgramExpression::SliceData(slice) => method(slice, "as_ptr"),
        ProgramExpression::SliceFromRawParts { data, count } => slice_call(
            crate::surface::RUST_SLICE_FROM_RAW_PARTS,
            vec![operand(data), operand(count)],
        ),
        _ => return None,
    })
}
