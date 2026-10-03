use super::schema::{Expression as E, Function, Record, RustExport, Statement as S, Type};
mod arrays;
mod chunks;
mod moves;
use crate::kernel::*;
use crate::languages::c::syntax::{C0Function, C0Parameter, C0StructLayout, C0Type};
use std::collections::{BTreeMap, BTreeSet};

pub(crate) type LoweredRust = (Vec<C0Function>, BTreeMap<String, C0StructLayout>);
fn scalar_type(t: &Type) -> Result<C0Type, String> {
    match t {
        Type::I32 => Ok(C0Type::Int32),
        Type::U8 => Ok(C0Type::UInt8),
        Type::U16 => Ok(C0Type::UInt16),
        Type::U32 => Ok(C0Type::UInt32),
        Type::Usize => Ok(C0Type::UInt64),
        Type::Bool => Ok(C0Type::Bool),
        Type::Unit => Ok(C0Type::Void),
        Type::Reference { pointee, .. } => match pointee.as_ref() {
            Type::I32 | Type::Record { .. } => Ok(C0Type::Int32Pointer),
            Type::U8 => Ok(C0Type::UInt8Pointer),
            Type::U16 => Ok(C0Type::UInt16Pointer),
            Type::U32 => Ok(C0Type::UInt32Pointer),
            Type::Array { element, .. } => match element.as_ref() {
                Type::I32 => Ok(C0Type::Int32Pointer),
                Type::U8 => Ok(C0Type::UInt8Pointer),
                Type::U32 => Ok(C0Type::UInt32Pointer),
                _ => Err("fixed arrays require i32, u8 or u32 elements".into()),
            },
            _ => Err("Rust reference pointee outside scalar/reference lowering".into()),
        },
        Type::Array { .. } => {
            Err("by-value Rust arrays as parameters or returns are not supported".into())
        }
        _ => Err("Rust value type outside direct scalar/reference lowering".into()),
    }
}
// Embedded arrays retain one ABI field and their concrete extent. Never
// flatten a field into one layout entry per element.
fn record_field_type(t: &Type) -> Result<C0Type, String> {
    let Type::Array { element, length } = t else {
        return scalar_type(t);
    };
    let element = scalar_type(element)?.to_kernel_type();
    let length = arrays::array_length(element, *length)?;
    Ok(match element {
        CType::Int32 => C0Type::Int32Array(length),
        CType::UInt8 => C0Type::UInt8Array(length),
        CType::UInt32 => C0Type::UInt32Array(length),
        _ => unreachable!(),
    })
}
fn array_field_parts(t: CType) -> Option<(CType, u32)> {
    match t {
        CType::Int32Array(n) => Some((CType::Int32, n)),
        CType::UInt8Array(n) => Some((CType::UInt8, n)),
        CType::UInt32Array(n) => Some((CType::UInt32, n)),
        _ => None,
    }
}
// Rust narrow unsigned casts truncate; the shared coercion requires a range
// proof. Mask first and use the existing checked coercion on that value.
fn rust_scalar_cast(value: CExpression, target: CType) -> CExpression {
    if matches!(target, CType::UInt8 | CType::UInt16) {
        c_cast(
            c_cast(
                c_bitwise_and(
                    c_cast(value, CType::UInt32),
                    c_uint32_literal(if target == CType::UInt8 { 255 } else { 65535 }),
                ),
                CType::Int32,
            ),
            target,
        )
    } else if target == CType::Int32 {
        // Rust narrowing retains the low word, then reinterprets its sign.
        c_cast(c_cast(value, CType::UInt32), CType::Int32)
    } else {
        c_cast(value, target)
    }
}
fn integer_from(value: CExpression, source: &Type, target: &Type) -> Result<CExpression, String> {
    let width = |t: &Type| match t {
        Type::U8 => Some(8),
        Type::U16 => Some(16),
        Type::U32 => Some(32),
        Type::Usize => Some(64),
        _ => None,
    };
    if !matches!((width(source), width(target)), (Some(a), Some(b)) if a <= b) {
        return Err("integer From requires a supported lossless unsigned conversion".into());
    }
    Ok(c_cast(value, scalar_type(target)?.to_kernel_type()))
}
pub(crate) fn lower(export: &RustExport) -> Result<LoweredRust, String> {
    let mut layouts = BTreeMap::new();
    let mut fields = BTreeMap::new();
    for record in &export.records {
        let mut layout_fields = record
            .fields
            .iter()
            .map(|f| {
                Ok((
                    f.name.clone(),
                    record_field_type(&f.value_type)?,
                    f.offset,
                    record_field_type(&f.value_type)?
                        .to_kernel_type()
                        .byte_width(),
                ))
            })
            .collect::<Result<Vec<_>, String>>()?;
        // Rust may reorder fields; declaration order still selects constructor
        // operands, while layout validation consumes physical offset order.
        layout_fields.sort_by_key(|f| f.2);
        let layout =
            C0StructLayout::from_explicit_fields(layout_fields, record.size, record.alignment)?;
        if layouts.insert(record.name.clone(), layout).is_some() {
            return Err("duplicate Rust record".into());
        }
        for f in &record.fields {
            if fields
                .insert(
                    (record.name.as_str(), f.name.as_str()),
                    (f.offset, record_field_type(&f.value_type)?.to_kernel_type()),
                )
                .is_some()
            {
                return Err("duplicate Rust field".into());
            }
        }
    }
    let record_index = export
        .records
        .iter()
        .map(|r| (r.name.as_str(), r))
        .collect::<BTreeMap<_, _>>();
    let function_index = export
        .functions
        .iter()
        .map(|f| (f.name.as_str(), f))
        .collect::<BTreeMap<_, _>>();
    let mut names = BTreeSet::new();
    let mut functions = Vec::new();
    for f in &export.functions {
        if !names.insert(f.name.clone()) {
            return Err("duplicate Rust function name".into());
        }
        functions.push(lower_function(
            export,
            f,
            &fields,
            &layouts,
            &record_index,
            &function_index,
        )?);
    }
    Ok((functions, layouts))
}
fn lower_function(
    export: &RustExport,
    f: &Function,
    fields: &BTreeMap<(&str, &str), (u32, CType)>,
    layouts: &BTreeMap<String, C0StructLayout>,
    records: &BTreeMap<&str, &Record>,
    functions: &BTreeMap<&str, &Function>,
) -> Result<C0Function, String> {
    if !matches!(
        f.return_type,
        Type::I32 | Type::U8 | Type::U16 | Type::U32 | Type::Usize | Type::Bool | Type::Unit
    ) {
        return Err("Rust reference/aggregate returns are not supported".into());
    }
    let return_type = scalar_type(&f.return_type)?;
    let mut parameters = Vec::new();
    let mut kernel_parameters = Vec::new();
    let mut locals = BTreeSet::new();
    let mut slices = BTreeMap::new();
    let mut arrays = BTreeMap::new();
    let mut references = BTreeMap::new();
    for p in &f.parameters {
        if !locals.insert(p.name.clone()) {
            return Err("duplicate Rust parameter".into());
        }
        if let Type::ByteSlice { mutable } = &p.value_type {
            let length = format!("{}_len", p.name);
            if f.parameters.iter().any(|other| other.name == length)
                || !locals.insert(length.clone())
            {
                return Err(format!(
                    "Rust slice length parameter `{length}` collides with a parameter"
                ));
            }
            slices.insert(p.name.clone(), (length.clone(), !mutable));
            parameters.push(
                C0Parameter::new(C0Type::UInt8Pointer, p.name.clone(), None)
                    .with_pointee_constant(!mutable),
            );
            parameters.push(C0Parameter::new(C0Type::UInt64, length.clone(), None));
            kernel_parameters
                .push(c_parameter(&p.name, CType::UInt8Pointer).with_pointee_constant(!mutable));
            kernel_parameters.push(c_parameter(length, CType::UInt64));
            continue;
        }
        if let Type::Reference { mutable, .. } = &p.value_type {
            references.insert(p.name.clone(), !mutable);
        }
        let c_type = scalar_type(&p.value_type)?;
        if let Type::Reference { mutable, pointee } = &p.value_type
            && let Type::Array { element, length } = pointee.as_ref()
        {
            let element = scalar_type(element)?.to_kernel_type();
            if *length > i32::MAX as u64 / u64::from(element.byte_width()) {
                return Err("fixed array storage exceeds the signed-word memory model".into());
            }
            arrays.insert(p.name.clone(), (*length, element, !mutable));
        }
        if c_type == C0Type::Void {
            return Err("unit parameters outside Rust slice".into());
        }
        let (tag, constant) = match &p.value_type {
            Type::Reference { mutable, pointee } => (
                match pointee.as_ref() {
                    Type::Record { name } => Some(name.clone()),
                    _ => None,
                },
                !mutable,
            ),
            _ => (None, false),
        };
        parameters
            .push(C0Parameter::new(c_type, p.name.clone(), tag).with_pointee_constant(constant));
        kernel_parameters
            .push(c_parameter(&p.name, c_type.to_kernel_type()).with_pointee_constant(constant));
    }
    let mut cx = Context {
        chunk_iterators: BTreeSet::new(),
        mir_chunk_iterators: BTreeSet::new(),
        chunk_options: BTreeSet::new(),
        local_arrays: BTreeSet::new(),
        owned_locals: BTreeSet::new(),
        slices,
        arrays,
        references,
        source: &export.logical_source,
        function: &f.name,
        fields,
        next_load: 0,
        next_temporary: 0,
        locals,
        return_type,
        layouts,
        records,
        functions,
    };
    let body = match &f.mir {
        Some(mir) if f.body.is_empty() => moves::lower(&mut cx, f, mir)?,
        Some(_) => return Err("Rust function must select exactly one body representation".into()),
        None => cx.body(&f.body)?,
    };
    let kernel = c_function(
        return_type.to_kernel_type(),
        &f.name,
        kernel_parameters,
        body,
    );
    let local_records = f
        .mir
        .as_ref()
        .map(|mir| {
            mir.locals
                .iter()
                .filter_map(|local| match &local.value_type {
                    Type::Record { name } => Some((local.name.clone(), name.clone())),
                    _ => None,
                })
                .collect()
        })
        .unwrap_or_default();
    Ok(
        C0Function::external(return_type, f.name.clone(), parameters)
            .with_local_struct_values(local_records)
            .with_prelowered_kernel_function(kernel),
    )
}
struct Context<'a> {
    chunk_iterators: BTreeSet<String>,
    mir_chunk_iterators: BTreeSet<String>,
    chunk_options: BTreeSet<String>,
    local_arrays: BTreeSet<String>,
    owned_locals: BTreeSet<String>,
    slices: BTreeMap<String, (String, bool)>,
    arrays: BTreeMap<String, (u64, CType, bool)>,
    references: BTreeMap<String, bool>,
    source: &'a str,
    function: &'a str,
    fields: &'a BTreeMap<(&'a str, &'a str), (u32, CType)>,
    next_load: u32,
    next_temporary: u32,
    locals: BTreeSet<String>,
    return_type: C0Type,
    layouts: &'a BTreeMap<String, C0StructLayout>,
    records: &'a BTreeMap<&'a str, &'a Record>,
    functions: &'a BTreeMap<&'a str, &'a Function>,
}
impl Context<'_> {
    fn body(&mut self, body: &[S]) -> Result<CStatement, String> {
        let mut result = c_skip();
        for s in body {
            result = c_seq(result, self.statement(s)?);
        }
        Ok(result)
    }
    fn statement(&mut self, s: &S) -> Result<CStatement, String> {
        match s {
            S::ChunkDeclare {
                iterator,
                slice,
                size,
            } => self.chunk_declare(iterator, slice, size),
            S::ChunkFor {
                iterator,
                binding,
                body,
            } => self.chunk_for(iterator, binding, body),
            S::SliceSplit {
                slice,
                midpoint,
                left,
                right,
            } => self.slice_split(slice, midpoint, left, right),
            S::SliceFor {
                iterator,
                slice,
                binding,
                by_reference,
                body,
            } => self.slice_for(iterator, slice, binding, *by_reference, body),
            S::Declare { place, initializer } => {
                if let Type::Reference { mutable, .. } = &place.value_type {
                    self.references.insert(place.name.clone(), !mutable);
                }
                if !self.locals.insert(place.name.clone()) {
                    return Err("duplicate Rust local identity".into());
                }
                if let Type::Array { element, length } = &place.value_type {
                    return self.declare_array(&place.name, element, *length, initializer);
                }
                if let Type::ByteSlice { mutable } = &place.value_type {
                    let (pointer, length_value) = self.slice_parts(initializer)?;
                    let length = format!("{}_len", place.name);
                    if !self.locals.insert(length.clone()) {
                        return Err("slice local length collision".into());
                    }
                    self.slices
                        .insert(place.name.clone(), (length.clone(), !mutable));
                    return Ok(c_seq(
                        c_declare_with_all_qualifiers(
                            &place.name,
                            CType::UInt8Pointer,
                            false,
                            false,
                            false,
                            !mutable,
                        ),
                        c_seq(
                            c_declare(&length, CType::UInt64),
                            c_seq(
                                c_assign(
                                    &place.name,
                                    c_cast_with_pointee_qualifiers(
                                        pointer,
                                        CType::UInt8Pointer,
                                        false,
                                        !mutable,
                                    ),
                                ),
                                c_assign(length, length_value),
                            ),
                        ),
                    ));
                }
                if let Type::Reference { mutable, pointee } = &place.value_type
                    && let Type::Array { element, length } = pointee.as_ref()
                {
                    let (pointer, source_length, source_element) =
                        self.indexed_parts(initializer)?;
                    if source_length != c_uint64_literal(*length)
                        || source_element != scalar_type(element)?.to_kernel_type()
                    {
                        return Err("fixed array local disagrees with initializer".into());
                    }
                    let t = scalar_type(&place.value_type)?.to_kernel_type();
                    self.arrays
                        .insert(place.name.clone(), (*length, source_element, !mutable));
                    return Ok(c_seq(
                        c_declare_with_all_qualifiers(
                            &place.name,
                            t,
                            false,
                            false,
                            false,
                            !mutable,
                        ),
                        c_assign(
                            &place.name,
                            c_cast_with_pointee_qualifiers(pointer, t, false, !mutable),
                        ),
                    ));
                }
                let t = scalar_type(&place.value_type)?;
                if t == C0Type::Void {
                    return Err("unit locals outside Rust slice".into());
                }
                let constant = matches!(place.value_type, Type::Reference { mutable: false, .. });
                let declaration = c_declare_with_all_qualifiers(
                    &place.name,
                    t.to_kernel_type(),
                    false,
                    false,
                    false,
                    constant,
                );
                let assign = self.assign(&place.name, initializer)?;
                Ok(c_seq(declaration, assign))
            }
            S::Assign {
                target: E::Local { name },
                value,
            } => self.assign(name, value),
            S::Assign { target, value } => {
                if let E::Deref {
                    value_type: Type::Array { element, length },
                    ..
                } = target
                {
                    let (checks, pointer) = self.prepared_address(target)?;
                    return Ok(c_seq(
                        checks,
                        self.assign_array(
                            pointer,
                            scalar_type(element)?.to_kernel_type(),
                            *length,
                            value,
                        )?,
                    ));
                }
                let (mut checks, mut value) = self.prepared_expr(value)?;
                if matches!(target, E::Index { .. }) {
                    // Rust evaluates the RHS before the destination index,
                    // which may call a function that changes the RHS storage.
                    let value_type = match self.place_type(target)? {
                        CType::UInt8 => Type::U8,
                        CType::UInt32 => Type::U32,
                        CType::Int32 => Type::I32,
                        _ => return Err("unsupported Rust indexed assignment type".into()),
                    };
                    let (capture, name) = self.capture_operand(value, &value_type)?;
                    checks = c_seq(checks, capture);
                    value = c_variable(name);
                }
                let (target_checks, address) = self.prepared_address(target)?;
                Ok(c_seq(
                    c_seq(checks, target_checks),
                    c_typed_store(address, value, self.place_type(target)?),
                ))
            }
            S::While { condition, body } => {
                fn simple_guard(expression: &E) -> bool {
                    match expression {
                        E::Integer { .. }
                        | E::UnsignedInteger { .. }
                        | E::UsizeInteger { .. }
                        | E::Boolean { .. }
                        | E::Local { .. }
                        | E::SliceLength { .. } => true,
                        E::Not { value } | E::Cast { value, .. } | E::IntegerFrom { value, .. } => {
                            simple_guard(value)
                        }
                        E::Binary {
                            operator,
                            left,
                            right,
                            ..
                        } => {
                            matches!(
                                operator.as_str(),
                                "eq" | "ne" | "lt" | "le" | "gt" | "ge" | "and" | "or"
                            ) && simple_guard(left)
                                && simple_guard(right)
                        }
                        _ => false,
                    }
                }
                if !simple_guard(condition) {
                    return Err("Rust while conditions currently require scalar comparisons without calls, indexing or arithmetic".into());
                }
                Ok(c_while(self.expr(condition)?, Vec::new(), self.body(body)?))
            }
            S::If {
                condition,
                then_body,
                else_body,
            } => {
                let (checks, condition) = self.prepared_expr(condition)?;
                Ok(c_seq(
                    checks,
                    c_if(condition, self.body(then_body)?, self.body(else_body)?),
                ))
            }
            S::Return {
                value:
                    Some(E::Call {
                        function,
                        arguments,
                    }),
            } => {
                let mut name = "__rust_return_value".to_string();
                while self.locals.contains(&name) {
                    name.push('_');
                }
                self.locals.insert(name.clone());
                let (checks, arguments) = self.prepared_arguments(function, arguments)?;
                Ok(c_seq(
                    checks,
                    c_seq(
                        c_declare(&name, self.return_type.to_kernel_type()),
                        c_seq(
                            c_call_assign(&name, function, arguments),
                            c_return(c_variable(name)),
                        ),
                    ),
                ))
            }
            S::Return { value: Some(value) } => {
                let (checks, value) = self.prepared_expr(value)?;
                Ok(c_seq(checks, c_return(value)))
            }
            S::Return { value: None } if self.return_type == C0Type::Void => {
                Ok(c_return(c_void_value()))
            }
            S::Return { value: None } => Err("missing Rust return value".into()),
            S::Call {
                function,
                arguments,
            } => {
                let (checks, arguments) = self.prepared_arguments(function, arguments)?;
                Ok(c_seq(checks, c_call(function, arguments)))
            }
        }
    }
    fn slice_split(
        &mut self,
        slice: &E,
        midpoint: &E,
        left: &super::schema::Place,
        right: &super::schema::Place,
    ) -> Result<CStatement, String> {
        let E::Local { name } = slice else {
            return Err("split_at requires a shared byte-slice local".into());
        };
        if !self.slices.get(name).is_some_and(|(_, constant)| *constant) {
            return Err("split_at requires a shared byte-slice local".into());
        }
        let (pointer, length) = self.slice_parts(slice)?;
        // Evaluate the receiver before the argument and capture both metadata
        // components. The midpoint may call code; it is evaluated only once.
        let (pointer_capture, pointer_name) = self.capture_operand(
            pointer,
            &Type::Reference {
                mutable: false,
                pointee: Box::new(Type::U8),
            },
        )?;
        let (length_capture, length_name) = self.capture_operand(length, &Type::Usize)?;
        let (midpoint_prefix, midpoint_value) = self.prepared_expr(midpoint)?;
        let (midpoint_capture, midpoint_name) =
            self.capture_operand(midpoint_value, &Type::Usize)?;
        let mut result = c_seq(
            pointer_capture,
            c_seq(length_capture, c_seq(midpoint_prefix, midpoint_capture)),
        );
        result = c_seq(
            result,
            c_labeled_assert(
                c_less_equal(c_variable(&midpoint_name), c_variable(&length_name)),
                "Rust split_at panic check",
            ),
        );
        // Pointer offsets use the shared signed-word memory model. Check the
        // full-width midpoint before narrowing; slice lengths remain usize.
        result = c_seq(
            result,
            c_labeled_assert(
                c_less_equal(
                    c_variable(&midpoint_name),
                    c_uint64_literal(i32::MAX as u64),
                ),
                "Rust split_at memory-model offset bound",
            ),
        );
        for (place, pointer, length) in [
            (left, c_variable(&pointer_name), c_variable(&midpoint_name)),
            (
                right,
                c_add(
                    c_variable(&pointer_name),
                    c_cast(
                        c_cast(c_variable(&midpoint_name), CType::UInt32),
                        CType::Int32,
                    ),
                ),
                c_subtract(c_variable(&length_name), c_variable(&midpoint_name)),
            ),
        ] {
            if place.value_type != (Type::ByteSlice { mutable: false }) {
                return Err("split_at results must be shared byte slices".into());
            }
            let length_name = format!("{}_len", place.name);
            if !self.locals.insert(place.name.clone()) || !self.locals.insert(length_name.clone()) {
                return Err("duplicate split_at local identity".into());
            }
            self.slices
                .insert(place.name.clone(), (length_name.clone(), true));
            result = c_seq(
                result,
                c_seq(
                    c_declare_with_all_qualifiers(
                        &place.name,
                        CType::UInt8Pointer,
                        false,
                        false,
                        false,
                        true,
                    ),
                    c_seq(
                        c_declare(&length_name, CType::UInt64),
                        c_seq(
                            c_assign(
                                &place.name,
                                c_cast_with_pointee_qualifiers(
                                    pointer,
                                    CType::UInt8Pointer,
                                    false,
                                    true,
                                ),
                            ),
                            c_assign(length_name, length),
                        ),
                    ),
                ),
            );
        }
        Ok(result)
    }
    // Semantic slice-iterator state: cursor plus remaining slice length.
    // The signed length is the shared memory model's checked representation,
    // not a generated count of processed elements.
    fn slice_for(
        &mut self,
        iterator: &str,
        slice: &E,
        binding: &super::schema::Place,
        by_reference: bool,
        body: &[S],
    ) -> Result<CStatement, String> {
        let (pointer, length) = self.slice_parts(slice)?;
        let cursor = format!("{iterator}_cursor");
        let remaining = format!("{iterator}_remaining");
        let item = format!("{iterator}_item");
        for name in [&cursor, &remaining, &item, &binding.name] {
            if !self.locals.insert(name.clone()) {
                return Err("Rust iterator state identity collision".into());
            }
        }
        let expected = if by_reference {
            Type::Reference {
                mutable: false,
                pointee: Box::new(Type::U8),
            }
        } else {
            Type::U8
        };
        if binding.value_type != expected {
            return Err("Rust iterator yielded binding type mismatch".into());
        }
        let declaration = c_declare_with_all_qualifiers(
            &binding.name,
            scalar_type(&binding.value_type)?.to_kernel_type(),
            false,
            false,
            false,
            by_reference,
        );
        // Save Some's shared address before advancing. Copy patterns likewise
        // read that address before the source body; None does neither operation.
        let yielded = if by_reference {
            c_variable(&item)
        } else {
            let occurrence = self.next_load;
            self.next_load = self
                .next_load
                .checked_add(1)
                .ok_or("Rust load identity exhausted")?;
            c_typed_load_with_source(
                c_variable(&item),
                CType::UInt8,
                Some(LoadSourceId {
                    owner: LoadSourceOwnerId {
                        source_unit: self.source.into(),
                        function: self.function.into(),
                    },
                    occurrence,
                }),
            )
        };
        let next = c_seq(
            c_declare_with_all_qualifiers(&item, CType::UInt8Pointer, false, false, false, true),
            c_seq(
                c_assign(&item, c_variable(&cursor)),
                c_seq(
                    c_assign(&cursor, c_add(c_variable(&cursor), c_int32_literal(1))),
                    c_seq(
                        c_assign(
                            &remaining,
                            c_subtract(c_variable(&remaining), c_int32_literal(1)),
                        ),
                        c_seq(declaration, c_assign(&binding.name, yielded)),
                    ),
                ),
            ),
        );
        let source_body = self.body(body)?;
        Ok(c_seq(
            c_labeled_assert(
                c_less_equal(length.clone(), c_uint64_literal(i32::MAX as u64)),
                "Rust iterator memory-model length bound",
            ),
            c_seq(
                c_declare_with_all_qualifiers(
                    &cursor,
                    CType::UInt8Pointer,
                    false,
                    false,
                    false,
                    true,
                ),
                c_seq(
                    c_assign(&cursor, pointer),
                    c_seq(
                        c_declare(&remaining, CType::Int32),
                        c_seq(
                            c_assign(
                                &remaining,
                                c_cast(c_cast(length, CType::UInt32), CType::Int32),
                            ),
                            c_while(
                                c_not(c_equal(c_variable(&remaining), c_int32_literal(0))),
                                Vec::new(),
                                c_seq(next, source_body),
                            ),
                        ),
                    ),
                ),
            ),
        ))
    }
    fn assign(&mut self, name: &str, e: &E) -> Result<CStatement, String> {
        if !self.locals.contains(name) {
            return Err(format!("unknown Rust local `{name}`"));
        }
        if self.local_arrays.contains(name) {
            let (length, element, _) = self.arrays[name];
            return self.assign_array(self.array_pointer(name)?, element, length, e);
        }
        if let Some((length, constant)) = self.slices.get(name).cloned() {
            let checks = self.chunk_slice_checks(e)?;
            let (pointer, length_value) = self.slice_parts(e)?;
            return Ok(c_seq(
                checks,
                c_seq(
                    c_assign(
                        name,
                        c_cast_with_pointee_qualifiers(
                            pointer,
                            CType::UInt8Pointer,
                            false,
                            constant,
                        ),
                    ),
                    c_assign(length, length_value),
                ),
            ));
        }
        if let Some((length, element, constant)) = self.arrays.get(name).copied() {
            let (pointer, source_length, source_element) = self.indexed_parts(e)?;
            if source_length != c_uint64_literal(length) || source_element != element {
                return Err("fixed array assignment disagrees with destination".into());
            }
            let pointer_type = match element {
                CType::Int32 => CType::Int32Pointer,
                CType::UInt8 => CType::UInt8Pointer,
                CType::UInt32 => CType::UInt32Pointer,
                _ => return Err("unsupported fixed array element".into()),
            };
            return Ok(c_assign(
                name,
                c_cast_with_pointee_qualifiers(pointer, pointer_type, false, constant),
            ));
        }
        match e {
            E::Call {
                function,
                arguments,
            } => {
                let (checks, arguments) = self.prepared_arguments(function, arguments)?;
                Ok(c_seq(checks, c_call_assign(name, function, arguments)))
            }
            _ => {
                let (checks, value) = self.prepared_expr(e)?;
                Ok(c_seq(checks, c_assign(name, value)))
            }
        }
    }
    fn prepared_arguments(
        &mut self,
        function: &str,
        args: &[E],
    ) -> Result<(CStatement, Vec<CExpression>), String> {
        let types = self
            .functions
            .get(function)
            .ok_or("missing Rust call definition")?
            .parameters
            .iter()
            .map(|p| p.value_type.clone())
            .collect::<Vec<_>>();
        if types.len() != args.len() {
            return Err("Rust call argument count disagrees with callee".into());
        }
        let mut checks = c_skip();
        let mut values = Vec::new();
        for (argument, value_type) in args.iter().zip(types) {
            if let Type::ByteSlice { mutable } = value_type {
                let (pointer, length) = self.slice_parts(argument)?;
                let (capture_pointer, pointer_name) = self.capture_operand(
                    pointer,
                    &Type::Reference {
                        mutable,
                        pointee: Box::new(Type::U8),
                    },
                )?;
                let (capture_length, length_name) = self.capture_operand(length, &Type::Usize)?;
                checks = c_seq(checks, c_seq(capture_pointer, capture_length));
                values.extend([c_variable(pointer_name), c_variable(length_name)]);
                continue;
            }
            let (prefix, value) = self.prepared_expr(argument)?;
            let (capture, name) = self.capture_operand(value, &value_type)?;
            checks = c_seq(checks, c_seq(prefix, capture));
            values.push(c_variable(name));
        }
        Ok((checks, values))
    }

    fn capture_operand(
        &mut self,
        value: CExpression,
        value_type: &Type,
    ) -> Result<(CStatement, String), String> {
        let name = loop {
            let name = format!("__rust_checked_{}", self.next_temporary);
            self.next_temporary = self
                .next_temporary
                .checked_add(1)
                .ok_or("Rust temporary identity exhausted")?;
            if self.locals.insert(name.clone()) {
                break name;
            }
        };
        let c_type = scalar_type(value_type)?.to_kernel_type();
        let constant = matches!(value_type, Type::Reference { mutable: false, .. });
        let value = if matches!(value_type, Type::Reference { .. }) {
            c_cast_with_pointee_qualifiers(value, c_type, false, constant)
        } else {
            c_cast(value, c_type)
        };
        Ok((
            c_seq(
                c_declare_with_all_qualifiers(&name, c_type, false, false, false, constant),
                c_assign(&name, value),
            ),
            name,
        ))
    }

    // Capture each operand once, in source order. Guards reference those
    // small names rather than duplicating arbitrarily large expression trees.
    // The generated asserts are checked execution obligations, not assumptions.
    fn prepared_expr(&mut self, e: &E) -> Result<(CStatement, CExpression), String> {
        match e {
            E::Call {
                function,
                arguments,
            } => {
                let return_type = self
                    .functions
                    .get(function.as_str())
                    .ok_or("missing Rust call definition")?
                    .return_type
                    .clone();
                let (prefix, arguments) = self.prepared_arguments(function, arguments)?;
                let (declare, name) = self.capture_operand(c_int32_literal(0), &return_type)?;
                Ok((
                    c_seq(
                        prefix,
                        c_seq(declare, c_call_assign(&name, function, arguments)),
                    ),
                    c_variable(name),
                ))
            }
            E::Index { .. } => {
                let (checks, pointer) = self.prepared_address(e)?;
                let occurrence = self.next_load;
                self.next_load = self
                    .next_load
                    .checked_add(1)
                    .ok_or("Rust load identity exhausted")?;
                Ok((
                    checks,
                    c_typed_load_with_source(
                        pointer,
                        self.place_type(e)?,
                        Some(LoadSourceId {
                            owner: LoadSourceOwnerId {
                                source_unit: self.source.into(),
                                function: self.function.into(),
                            },
                            occurrence,
                        }),
                    ),
                ))
            }
            E::Borrow { place, value_type } if matches!(place.as_ref(), E::Index { .. }) => {
                let (checks, pointer) = self.prepared_address(place)?;
                Ok((
                    checks,
                    c_cast(pointer, scalar_type(value_type)?.to_kernel_type()),
                ))
            }
            E::Binary {
                operator,
                left_type,
                right_type,
                left,
                right,
            } => {
                let (left_prefix, left_value) = self.prepared_expr(left)?;
                let (left_capture, left_name) = self.capture_operand(left_value, left_type)?;
                let prefix = c_seq(left_prefix, left_capture);
                if operator == "and" || operator == "or" {
                    if *left_type != Type::Bool || *right_type != Type::Bool {
                        return Err("Rust logical operators require bool operands".into());
                    }
                    let (right_prefix, right_value) = self.prepared_expr(right)?;
                    let condition = if operator == "and" {
                        c_variable(&left_name)
                    } else {
                        c_not(c_variable(&left_name))
                    };
                    let update = c_seq(
                        right_prefix,
                        c_assign(&left_name, c_cast(right_value, CType::Bool)),
                    );
                    return Ok((
                        c_seq(prefix, c_if(condition, update, c_skip())),
                        c_variable(left_name),
                    ));
                }
                let (right_prefix, right_value) = self.prepared_expr(right)?;
                let (right_capture, right_name) = self.capture_operand(right_value, right_type)?;
                let mut prefix = c_seq(prefix, c_seq(right_prefix, right_capture));
                if *left_type == Type::Usize {
                    let l = c_variable(&left_name);
                    let r = c_variable(&right_name);
                    let max = c_uint64_literal(u64::MAX);
                    // Stay unsigned at the full target width. Widening to
                    // signed i64 would lose half of the usize value range.
                    let obligation = match operator.as_str() {
                        "add" => Some(c_less_equal(l, c_subtract(max, r))),
                        "sub" => Some(c_greater_equal(l, r)),
                        "mul" => Some(c_or(
                            c_equal(r.clone(), c_uint64_literal(0)),
                            c_less_equal(l, c_divide(max, r)),
                        )),
                        "shl" | "shr" => {
                            Some(c_less_than(c_cast(r, CType::UInt64), c_uint64_literal(64)))
                        }
                        _ => None,
                    };
                    if let Some(obligation) = obligation {
                        prefix = c_seq(
                            prefix,
                            c_labeled_assert(obligation, format!("Rust {operator} panic check")),
                        );
                    }
                }
                if matches!(left_type, Type::U8 | Type::U16 | Type::U32) {
                    let l = c_cast(c_variable(&left_name), CType::UInt32);
                    let r = c_cast(c_variable(&right_name), CType::UInt32);
                    let width = match left_type {
                        Type::U8 => 8,
                        Type::U16 => 16,
                        _ => 32,
                    };
                    let maximum = match left_type {
                        Type::U8 => 255,
                        Type::U16 => 65535,
                        _ => u32::MAX,
                    };
                    let max = c_uint32_literal(maximum);
                    let obligation = match operator.as_str() {
                        "add" => Some(c_less_equal(
                            c_add(c_cast(l, CType::Int64), c_cast(r, CType::Int64)),
                            c_int64_literal(maximum as i64),
                        )),
                        "sub" => Some(c_greater_equal(l, r)),
                        "mul" => Some(c_or(
                            c_equal(r.clone(), c_uint32_literal(0)),
                            c_less_equal(l, c_divide(max, r)),
                        )),
                        "shl" | "shr" => Some(if *right_type == Type::Usize {
                            c_less_than(c_variable(&right_name), c_uint64_literal(width))
                        } else {
                            c_less_than(r, c_uint32_literal(width as u32))
                        }),
                        _ => None,
                    };
                    if let Some(obligation) = obligation {
                        prefix = c_seq(
                            prefix,
                            c_labeled_assert(obligation, format!("Rust {operator} panic check")),
                        );
                    }
                }
                let expression = E::Binary {
                    operator: operator.clone(),
                    left_type: left_type.clone(),
                    right_type: right_type.clone(),
                    left: Box::new(E::Local { name: left_name }),
                    right: Box::new(E::Local { name: right_name }),
                };
                Ok((prefix, self.expr(&expression)?))
            }
            E::Not { value }
            | E::BitwiseNot { value, .. }
            | E::Cast { value, .. }
            | E::IntegerFrom { value, .. } => {
                let (prefix, value) = self.prepared_expr(value)?;
                let value = match e {
                    E::Not { .. } => c_not(value),
                    E::BitwiseNot { value_type, .. } => rust_scalar_cast(
                        c_bitwise_not(value),
                        scalar_type(value_type)?.to_kernel_type(),
                    ),
                    E::Cast { value_type, .. } => {
                        rust_scalar_cast(value, scalar_type(value_type)?.to_kernel_type())
                    }
                    E::IntegerFrom {
                        source_type,
                        value_type,
                        ..
                    } => integer_from(value, source_type, value_type)?,
                    _ => unreachable!(),
                };
                Ok((prefix, value))
            }
            _ => Ok((c_skip(), self.expr(e)?)),
        }
    }
    fn slice_parts(&mut self, e: &E) -> Result<(CExpression, CExpression), String> {
        if let E::ChunkOptionSlice { option } = e {
            if !self.chunk_options.contains(option) {
                return Err("unknown chunk Option".into());
            }
            return Ok((
                c_variable(format!("{option}_pointer")),
                c_variable(format!("{option}_len")),
            ));
        }
        if let E::Borrow {
            place,
            value_type: Type::ByteSlice { mutable },
        } = e
        {
            let E::Local { name } = place.as_ref() else {
                return Err("slice reborrow requires a slice local".into());
            };
            if *mutable && self.slices.get(name).is_none_or(|(_, constant)| *constant) {
                return Err("mutable slice reborrow requires a mutable source".into());
            }
            return self.slice_parts(place);
        }
        if let E::ChunkRemainder { iterator } = e {
            if !self.chunk_iterators.contains(iterator) {
                return Err("unknown Rust chunk iterator".into());
            }
            return Ok((
                c_variable(format!("{iterator}_tail")),
                c_variable(format!("{iterator}_tail_len")),
            ));
        }
        if let E::ArrayToSlice { array, mutable } = e {
            let (pointer, length, element) = self.indexed_parts(array)?;
            if element != CType::UInt8 {
                return Err("array coercion requires u8 elements".into());
            }
            let constant = self.array_source_is_constant(array)?;
            if *mutable && constant {
                return Err("mutable array coercion requires a mutable source".into());
            }
            return Ok((pointer, length));
        }
        let E::Local { name } = e else {
            return Err("slice values must be local slice references".into());
        };
        let (length, _) = self
            .slices
            .get(name)
            .ok_or("unknown Rust slice reference")?;
        Ok((c_variable(name), c_variable(length)))
    }
    fn array_source_is_constant(&self, e: &E) -> Result<bool, String> {
        match e {
            E::Local { name } => self
                .arrays
                .get(name)
                .map(|a| a.2)
                .ok_or("unknown array source".into()),
            E::Deref { reference, .. } => self.array_source_is_constant(reference),
            E::Field { base, .. } => match base.as_ref() {
                E::Deref { reference, .. } => match reference.as_ref() {
                    E::Local { name } => self
                        .references
                        .get(name)
                        .copied()
                        .ok_or("unknown record reference".into()),
                    _ => Err("array field requires a record reference local".into()),
                },
                _ => Err("array field requires a borrowed record".into()),
            },
            E::Borrow {
                value_type: Type::Reference { mutable, .. },
                ..
            } => Ok(!mutable),
            _ => Err("array coercion requires a fixed array place".into()),
        }
    }
    fn indexed_parts(&mut self, e: &E) -> Result<(CExpression, CExpression, CType), String> {
        match e {
            E::Borrow { place, value_type } => {
                if matches!(value_type, Type::Reference { mutable: true, .. })
                    && self.array_source_is_constant(place)?
                {
                    return Err(
                        "mutable array field borrow requires a mutable record reference".into(),
                    );
                }
                self.indexed_parts(place)
            }
            E::Deref { reference, .. } => self.indexed_parts(reference),
            E::Local { name } if self.arrays.contains_key(name) => {
                let (length, element, _) = self.arrays[name];
                Ok((self.array_pointer(name)?, c_uint64_literal(length), element))
            }
            E::Field { record, field, .. } => {
                let (_, ty) = *self
                    .fields
                    .get(&(record.as_str(), field.as_str()))
                    .ok_or("unknown Rust array field")?;
                let (element, length) =
                    array_field_parts(ty).ok_or("indexed Rust field is not a scalar array")?;
                let constant = self.array_source_is_constant(e)?;
                let pointer_type = match element {
                    CType::Int32 => CType::Int32Pointer,
                    CType::UInt8 => CType::UInt8Pointer,
                    CType::UInt32 => CType::UInt32Pointer,
                    _ => unreachable!(),
                };
                let pointer = self.address(e)?;
                Ok((
                    c_cast_with_pointee_qualifiers(pointer, pointer_type, false, constant),
                    c_uint64_literal(u64::from(length)),
                    element,
                ))
            }
            _ => {
                let (pointer, length) = self.slice_parts(e)?;
                Ok((pointer, length, CType::UInt8))
            }
        }
    }
    fn array_pointer(&self, name: &str) -> Result<CExpression, String> {
        let (_, element, constant) = self.arrays.get(name).ok_or("unknown fixed array")?;
        let pointer_type = match element {
            CType::UInt8 => CType::UInt8Pointer,
            CType::UInt32 => CType::UInt32Pointer,
            CType::Int32 => CType::Int32Pointer,
            _ => return Err("unsupported fixed array element".into()),
        };
        Ok(c_cast_with_pointee_qualifiers(
            c_variable(name),
            pointer_type,
            false,
            *constant,
        ))
    }
    fn prepared_address(&mut self, e: &E) -> Result<(CStatement, CExpression), String> {
        if let E::Index { slice, index } = e {
            let (pointer, length, _) = self.indexed_parts(slice)?;
            let (checks, value) = self.prepared_expr(index)?;
            let (capture, name) = self.capture_operand(value, &Type::Usize)?;
            let index = c_variable(name);
            // Fixed-array extents have already been checked against signed-word
            // storage. Only after the full-width Rust bound below succeeds may
            // their index use the shared model's signed-word offset.
            let offset = if matches!(
                length,
                CExpression::Value(CValue::UInt64(Bitvector32Term::UInt64Constant(_)))
            ) {
                c_cast(c_cast(index.clone(), CType::UInt32), CType::Int32)
            } else {
                index.clone()
            };
            return Ok((
                c_seq(
                    checks,
                    c_seq(
                        capture,
                        c_labeled_assert(
                            c_less_than(index.clone(), length),
                            if matches!(slice.as_ref(), E::Local { name } if self.slices.contains_key(name))
                            {
                                "Rust slice index panic check"
                            } else {
                                "Rust array index panic check"
                            },
                        ),
                    ),
                ),
                c_add(pointer, offset),
            ));
        }
        Ok((c_skip(), self.address(e)?))
    }
    fn address(&mut self, e: &E) -> Result<CExpression, String> {
        match e {
            E::Local { name } if self.local_arrays.contains(name) => self.array_pointer(name),
            E::Deref { reference, .. } => self.expr(reference),
            E::Field {
                base,
                record,
                field,
            } => {
                let (offset, _) = *self
                    .fields
                    .get(&(record.as_str(), field.as_str()))
                    .ok_or("unknown Rust field")?;
                // Field bases are either record references or local stack objects.
                let pointer = match base.as_ref() {
                    E::Deref { reference, .. } => self.expr(reference)?,
                    _ => self.expr(base)?,
                };
                Ok(c_pointer_offset_bytes(pointer, offset))
            }
            E::Local { name } if self.owned_locals.contains(name) => {
                Ok(c_cast(c_variable(name), CType::Int32Pointer))
            }
            _ => Err("only reference-backed Rust places can be borrowed or stored".into()),
        }
    }
    fn place_type(&mut self, e: &E) -> Result<CType, String> {
        match e {
            E::Index { slice, .. } => Ok(self.indexed_parts(slice)?.2),
            E::Field { record, field, .. } => self
                .fields
                .get(&(record.as_str(), field.as_str()))
                .map(|(_, t)| *t)
                .ok_or("unknown Rust field type".into()),
            E::Deref { value_type, .. } => Ok(scalar_type(value_type)?.to_kernel_type()),
            _ => Err("unsupported Rust memory place type".into()),
        }
    }
    fn expr(&mut self, e: &E) -> Result<CExpression, String> {
        match e {
            E::ChunkHasNext { iterator } => self.chunk_has_next(iterator),
            E::ChunkOptionTag { option } => {
                if !self.chunk_options.contains(option) {
                    return Err("unknown chunk Option".into());
                }
                Ok(c_variable(format!("{option}_some")))
            }
            E::ChunkOptionSlice { .. } | E::ChunkRemainder { .. } | E::ArrayToSlice { .. } => {
                Err("Rust slices require pointer-plus-length preparation".into())
            }
            E::Array { .. } | E::Repeat { .. } => {
                Err("array values require whole-array assignment".into())
            }
            E::Integer { value } => Ok(c_int32_literal(*value as u32)),
            E::UsizeInteger { value } => Ok(c_uint64_literal(*value)),
            E::SliceLength { slice } => Ok(self.indexed_parts(slice)?.1),
            E::Index { .. } => Err("indexed Rust places require checked preparation".into()),
            E::UnsignedInteger { value, value_type } => match value_type {
                Type::U8 => Ok(c_uint8_literal(
                    u8::try_from(*value).map_err(|_| "Rust u8 literal out of range")?,
                )),
                Type::U16 => Ok(c_cast(
                    c_int32_literal(
                        u16::try_from(*value).map_err(|_| "Rust u16 literal out of range")? as u32,
                    ),
                    CType::UInt16,
                )),
                Type::U32 => Ok(c_uint32_literal(*value)),
                _ => Err("unsigned literal needs an unsigned Rust type".into()),
            },
            E::Boolean { value } => Ok(c_int32_literal(u32::from(*value))),
            E::IntegerFrom {
                value,
                source_type,
                value_type,
            } => {
                let value = self.expr(value)?;
                integer_from(value, source_type, value_type)
            }
            E::Local { name } => {
                if !self.locals.contains(name) {
                    return Err(format!("unknown Rust local `{name}`"));
                }
                Ok(c_variable(name))
            }
            E::Not { value } => Ok(c_not(self.expr(value)?)),
            E::Borrow { place, value_type } => {
                if let E::Field { record, field, .. } = place.as_ref()
                    && self
                        .fields
                        .get(&(record.as_str(), field.as_str()))
                        .is_some_and(|(_, ty)| array_field_parts(*ty).is_some())
                    && matches!(value_type, Type::Reference { mutable: true, .. })
                    && self.array_source_is_constant(place)?
                {
                    return Err(
                        "mutable array field borrow requires a mutable record reference".into(),
                    );
                }
                Ok(c_cast(
                    self.address(place)?,
                    scalar_type(value_type)?.to_kernel_type(),
                ))
            }
            E::Cast { value, value_type } => Ok(rust_scalar_cast(
                self.expr(value)?,
                scalar_type(value_type)?.to_kernel_type(),
            )),
            E::BitwiseNot { value, value_type } => Ok(rust_scalar_cast(
                c_bitwise_not(self.expr(value)?),
                scalar_type(value_type)?.to_kernel_type(),
            )),
            E::Deref { .. } | E::Field { .. } => {
                if array_field_parts(self.place_type(e)?).is_some() {
                    return Err("array fields must be borrowed or indexed; owned field copies are unsupported".into());
                }
                let pointer = self.address(e)?;
                let occurrence = self.next_load;
                self.next_load = self
                    .next_load
                    .checked_add(1)
                    .ok_or("Rust load identity exhausted")?;
                Ok(c_typed_load_with_source(
                    pointer,
                    self.place_type(e)?,
                    Some(LoadSourceId {
                        owner: LoadSourceOwnerId {
                            source_unit: self.source.into(),
                            function: self.function.into(),
                        },
                        occurrence,
                    }),
                ))
            }
            E::Binary {
                operator,
                left_type,
                left,
                right,
                ..
            } => {
                if matches!(operator.as_str(), "shl" | "shr")
                    && !matches!(left_type, Type::U8 | Type::U16 | Type::U32 | Type::Usize)
                {
                    return Err(
                        "Rust shifts currently require u8, u16, u32 or usize operands".into(),
                    );
                }
                let mut l = self.expr(left)?;
                let r = self.expr(right)?;
                // Keep the RHS at its source width. The shared shift evaluator
                // checks signed/nonnegative and full-width upper bounds before
                // forming its word-sized shift term. Narrowing here would lose
                // the exact relation to Rust's already checked count.
                if matches!(left_type, Type::U8 | Type::U16) {
                    // Rust narrow unsigned operations use unsigned words;
                    // the checked result is coerced to its original width.
                    l = c_cast(l, CType::UInt32);
                }
                let result = match operator.as_str() {
                    "add" => c_add(l, r),
                    "sub" => c_subtract(l, r),
                    "mul" => c_multiply(l, r),
                    "div" => c_divide(l, r),
                    "rem" => c_remainder(l, r),
                    "shl" => c_shift_left(l, r),
                    "shr" => c_shift_right(l, r),
                    "bit_and" => c_bitwise_and(l, r),
                    "bit_or" => c_bitwise_or(l, r),
                    "bit_xor" => c_bitwise_xor(l, r),
                    "eq" => c_equal(l, r),
                    "ne" => c_not_equal(l, r),
                    "lt" => c_less_than(l, r),
                    "le" => c_less_equal(l, r),
                    "gt" => c_greater_than(l, r),
                    "ge" => c_greater_equal(l, r),
                    "and" => c_and(l, r),
                    "or" => c_or(l, r),
                    _ => return Err("unsupported Rust operator in artifact".into()),
                };
                if matches!(
                    operator.as_str(),
                    "eq" | "ne" | "lt" | "le" | "gt" | "ge" | "and" | "or"
                ) {
                    Ok(result)
                } else if matches!(left_type, Type::U8 | Type::U16)
                    && matches!(operator.as_str(), "add" | "sub" | "mul" | "div" | "rem")
                {
                    // Checked narrow arithmetic cannot discard bits. Its range
                    // obligation permits an exact coercion; only casts,
                    // bitwise results and shifts need explicit truncation.
                    Ok(c_cast(
                        c_cast(result, CType::Int32),
                        scalar_type(left_type)?.to_kernel_type(),
                    ))
                } else {
                    Ok(rust_scalar_cast(
                        result,
                        scalar_type(left_type)?.to_kernel_type(),
                    ))
                }
            }
            E::Call { .. } => Err("nested Rust calls outside statement lowering".into()),
        }
    }
}
