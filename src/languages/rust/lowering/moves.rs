//! Compiler drop CFGs emit shared joins and supported natural while loops once. Checked live flags consume
//! a whole value on move/drop and reject duplicate cleanup even when scalar
//! field bits remain in old storage.
use super::*;
mod flow;
use crate::languages::rust::schema::{MirBody, MirStatement as S, MirTerminator as T};

pub(super) fn lower(
    cx: &mut Context<'_>,
    f: &Function,
    mir: &MirBody,
) -> Result<CStatement, String> {
    let mut records = BTreeMap::new();
    let mut live = BTreeMap::new();
    let mut declarations = c_skip();
    for (index, local) in mir.locals.iter().enumerate() {
        if !cx.locals.insert(local.name.clone()) {
            return Err("duplicate MIR local identity".into());
        }
        let statement = match &local.value_type {
            Type::Unit => c_skip(),
            Type::Record { name } => {
                cx.owned_locals.insert(local.name.clone());
                let flag = format!("__rust_owned_live_{index}");
                if !cx.locals.insert(flag.clone()) {
                    return Err("MIR live flag collides with a source name".into());
                }
                records.insert(local.name.as_str(), name.as_str());
                live.insert(local.name.as_str(), flag.clone());
                // Construction grants authority over fresh stack bytes. The
                // live flag stays false until every typed field is overwritten;
                // source reads cannot observe the kernel's fresh placeholders.
                c_seq(
                    c_declare(flag.clone(), CType::Int32),
                    c_seq(
                        c_assign(flag, c_int32_literal(0)),
                        c_begin_aggregate_construction(
                            local.name.clone(),
                            cx.layouts
                                .get(name.as_str())
                                .ok_or("missing owned record layout")?
                                .to_kernel_aggregate_layout(),
                        ),
                    ),
                )
            }
            Type::ByteSlice { mutable } => {
                let length = format!("{}_len", local.name);
                if !cx.locals.insert(length.clone()) {
                    return Err("MIR slice local length collision".into());
                }
                cx.slices
                    .insert(local.name.clone(), (length.clone(), !mutable));
                c_seq(
                    c_declare_with_all_qualifiers(
                        &local.name,
                        CType::UInt8Pointer,
                        false,
                        false,
                        false,
                        !mutable,
                    ),
                    c_declare(length, CType::UInt64),
                )
            }
            Type::Array { element, length } => {
                let element = scalar_type(element)?.to_kernel_type();
                if !matches!(element, CType::Int32 | CType::UInt8 | CType::UInt32)
                    || *length > i32::MAX as u64 / u64::from(element.byte_width())
                {
                    return Err(
                        "compact arrays require i32/u8/u32 elements and signed-word storage".into(),
                    );
                }
                cx.local_arrays.insert(local.name.clone());
                cx.arrays
                    .insert(local.name.clone(), (*length, element, false));
                c_begin_aggregate_construction(
                    local.name.clone(),
                    CAggregateLayout::new(
                        *length as u32 * element.byte_width(),
                        element.byte_width(),
                        vec![],
                    ),
                )
            }
            t => c_declare(local.name.clone(), scalar_type(t)?.to_kernel_type()),
        };
        declarations = c_seq(declarations, statement);
    }
    if mir.blocks.is_empty() {
        return Err("MIR body has no entry block".into());
    }
    let flow = flow::Flow::analyze(f, mir)?;
    let mut nodes = vec![None; mir.blocks.len()];
    let check = |local: &str, record: &str| -> Result<&str, String> {
        if records.get(local).copied() != Some(record) {
            return Err("owned MIR place disagrees with record type".into());
        }
        live.get(local)
            .map(String::as_str)
            .ok_or("unknown owned MIR place".into())
    };
    let assertion = |flag: &str, is_live: bool| {
        c_assert(c_equal(
            c_variable(flag),
            c_int32_literal(u32::from(is_live)),
        ))
    };
    for &block in &flow.order {
        let terminal = match &mir.blocks[block].terminator {
            T::Goto { .. } => c_skip(),
            T::If { condition, .. } => accesses(&[condition], &live),
            T::Return => {
                let mut end = if f.return_type == Type::Unit {
                    c_return(c_void_value())
                } else {
                    c_return(c_variable("__rust_mir_0"))
                };
                // Plain values without a destructor can die at Return; any
                // destructor-bearing value must already have been consumed.
                for (local, record) in &records {
                    if cx
                        .records
                        .get(record)
                        .ok_or("missing record")?
                        .destructor
                        .is_some()
                    {
                        end = c_seq(assertion(&live[*local], false), end);
                    }
                }
                end
            }
            T::Unreachable => c_assert(c_int32_literal(0)),
            T::Drop { local, record, .. } => {
                let flag = check(local, record)?;
                let r = cx.records.get(record.as_str()).ok_or("unknown drop type")?;
                let cleanup = match &r.destructor {
                    Some(dtor) if cx.functions.contains_key(dtor.as_str()) => {
                        c_call(dtor, vec![c_cast(c_variable(local), CType::Int32Pointer)])
                    }
                    Some(_) => {
                        return Err("destructor body missing from prepared Rust input".into());
                    }
                    None => c_skip(),
                };
                c_seq(
                    assertion(flag, true),
                    c_seq(cleanup, c_assign(flag, c_int32_literal(0))),
                )
            }
            T::Call {
                function,
                arguments,
                destination,
                ..
            } => {
                let callee = cx
                    .functions
                    .get(function.as_str())
                    .ok_or("missing MIR call definition")?;
                let (prefix, arguments_values) = cx.prepared_arguments(function, arguments)?;
                let call = if callee.return_type == Type::Unit {
                    c_call(function, arguments_values)
                } else {
                    c_call_assign(destination, function, arguments_values)
                };
                c_seq(
                    accesses(&arguments.iter().collect::<Vec<_>>(), &live),
                    c_seq(prefix, call),
                )
            }
        };
        let mut statements = c_skip();
        for s in &mir.blocks[block].statements {
            let statement = match s {
                S::Assign {
                    target: E::Local { name },
                    value,
                } if cx.local_arrays.contains(name) => {
                    let (length, element, _) = cx.arrays[name];
                    let pointer = cx.array_pointer(name)?;
                    match value {
                        E::Array { .. } => cx.assign_array(pointer, element, length, value)?,
                        E::Repeat {
                            value,
                            length: count,
                        } if *count == length => {
                            let (checks, value) = cx.prepared_expr(value)?;
                            c_seq(
                                checks,
                                c_initialize_scalar_array(
                                    pointer,
                                    value,
                                    element,
                                    length as u32,
                                    false,
                                ),
                            )
                        }
                        E::Repeat { .. } => {
                            return Err("array repeat length disagrees with destination".into());
                        }
                        value => {
                            let (source, count, source_element) = cx.indexed_parts(value)?;
                            if count != c_uint64_literal(length) || source_element != element {
                                return Err("array copy type disagrees with destination".into());
                            }
                            c_initialize_scalar_array(pointer, source, element, length as u32, true)
                        }
                    }
                }
                S::Assign {
                    target: E::Local { name },
                    value,
                } if !records.contains_key(name.as_str()) => cx.assign(name, value)?,
                S::Assign { target, value } => {
                    let (mut checks, mut value) = cx.prepared_expr(value)?;
                    if matches!(target, E::Index { .. }) {
                        let value_type = match cx.place_type(target)? {
                            CType::UInt8 => Type::U8,
                            CType::UInt32 => Type::U32,
                            CType::Int32 => Type::I32,
                            _ => return Err("unsupported Rust indexed assignment type".into()),
                        };
                        let (capture, name) = cx.capture_operand(value, &value_type)?;
                        checks = c_seq(checks, capture);
                        value = c_variable(name);
                    }
                    let (target_checks, address) = cx.prepared_address(target)?;
                    c_seq(
                        c_seq(checks, target_checks),
                        c_typed_store(address, value, cx.place_type(target)?),
                    )
                }
                S::Initialize {
                    target,
                    record,
                    fields,
                } => {
                    let flag = check(target, record)?;
                    let r = cx
                        .records
                        .get(record.as_str())
                        .ok_or("unknown constructor record")?;
                    if fields.len() != r.fields.len() {
                        return Err("partial record initialization".into());
                    }
                    let mut initialize = assertion(flag, false);
                    for (value, field) in fields.iter().zip(&r.fields) {
                        initialize = c_seq(
                            initialize,
                            c_typed_store(
                                c_pointer_offset_bytes(c_variable(target), field.offset),
                                cx.expr(value)?,
                                scalar_type(&field.value_type)?.to_kernel_type(),
                            ),
                        );
                    }
                    c_seq(initialize, c_assign(flag, c_int32_literal(1)))
                }
                S::Move {
                    target,
                    source,
                    record,
                } => {
                    if target == source {
                        return Err("self move is invalid".into());
                    }
                    let source_flag = check(source, record)?;
                    let target_flag = check(target, record)?;
                    let mut copy =
                        c_seq(assertion(source_flag, true), assertion(target_flag, false));
                    for field in &cx
                        .records
                        .get(record.as_str())
                        .ok_or("missing moved record")?
                        .fields
                    {
                        let read = E::Field {
                            base: Box::new(E::Local {
                                name: source.clone(),
                            }),
                            record: record.clone(),
                            field: field.name.clone(),
                        };
                        copy = c_seq(
                            copy,
                            c_typed_store(
                                c_pointer_offset_bytes(c_variable(target), field.offset),
                                cx.expr(&read)?,
                                scalar_type(&field.value_type)?.to_kernel_type(),
                            ),
                        );
                    }
                    c_seq(
                        copy,
                        c_seq(
                            c_assign(source_flag, c_int32_literal(0)),
                            c_assign(target_flag, c_int32_literal(1)),
                        ),
                    )
                }
                S::EndStorage { local } => match records.get(local.as_str()) {
                    Some(record) => {
                        let flag = check(local, record)?;
                        if cx
                            .records
                            .get(record)
                            .ok_or("missing record")?
                            .destructor
                            .is_some()
                        {
                            assertion(flag, false)
                        } else {
                            c_assign(flag, c_int32_literal(0))
                        }
                    }
                    None => c_skip(),
                },
            };
            let inputs: Vec<&E> = match s {
                S::Assign { target, value } => vec![target, value],
                S::Initialize { fields, .. } => fields.iter().collect(),
                _ => Vec::new(),
            };
            statements = c_seq(statements, c_seq(accesses(&inputs, &live), statement));
        }
        nodes[block] = Some(c_seq(statements, terminal));
    }
    let mut emitted = vec![false; mir.blocks.len()];
    let structured = region(cx, mir, &nodes, &flow, &mut emitted, 0, mir.blocks.len())?;
    Ok(c_seq(declarations, structured))
}

fn successors(t: &T, exit: usize) -> Vec<usize> {
    match t {
        T::Goto { target } | T::Drop { target, .. } | T::Call { target, .. } => vec![*target],
        T::If {
            then_target,
            else_target,
            ..
        } => vec![*then_target, *else_target],
        _ => vec![exit],
    }
}
// A reverse topological pass builds the postdominator tree. Binary lifting
// keeps each merge logarithmic; no path enumeration or graph-wide set clones.
#[cfg(test)]
fn postdominators(mir: &MirBody, order: &[usize]) -> Vec<usize> {
    let graph = mir
        .blocks
        .iter()
        .map(|b| successors(&b.terminator, mir.blocks.len()))
        .collect::<Vec<_>>();
    graph_postdominators(&graph, order)
}
fn graph_postdominators(graph: &[Vec<usize>], order: &[usize]) -> Vec<usize> {
    let exit = graph.len();
    let levels = (usize::BITS - (exit + 1).leading_zeros()) as usize;
    let mut ancestors = vec![vec![exit; levels]; exit + 1];
    let mut depths = vec![0usize; exit + 1];
    let mut joins = vec![exit; exit];
    for &block in order {
        let targets = &graph[block];
        let mut a = targets[0];
        for &b in &targets[1..] {
            let mut b = b;
            if depths[a] < depths[b] {
                std::mem::swap(&mut a, &mut b);
            }
            let mut difference = depths[a] - depths[b];
            while difference != 0 {
                let bit = difference.trailing_zeros() as usize;
                a = ancestors[a][bit];
                difference &= difference - 1;
            }
            if a != b {
                for bit in (0..levels).rev() {
                    if ancestors[a][bit] != ancestors[b][bit] {
                        a = ancestors[a][bit];
                        b = ancestors[b][bit];
                    }
                }
                a = ancestors[a][0];
            }
        }
        joins[block] = a;
        depths[block] = depths[a] + 1;
        ancestors[block][0] = a;
        for bit in 1..levels {
            ancestors[block][bit] = ancestors[ancestors[block][bit - 1]][bit - 1];
        }
    }
    joins
}
fn region(
    cx: &mut Context<'_>,
    mir: &MirBody,
    nodes: &[Option<CStatement>],
    flow: &flow::Flow,
    emitted: &mut [bool],
    mut block: usize,
    stop: usize,
) -> Result<CStatement, String> {
    let mut result = c_skip();
    while block != stop && block != mir.blocks.len() {
        if std::mem::replace(&mut emitted[block], true) {
            return Err("unstructured shared MIR region outside move/drop slice".into());
        }
        if let Some(loop_) = flow.loops.get(&block) {
            let T::If { condition, .. } = &mir.blocks[block].terminator else {
                return Err("natural while header is not conditional".into());
            };
            let body = region(cx, mir, nodes, flow, emitted, loop_.body, block)?;
            let condition = flow::header_condition(mir, block, condition, &flow.scalar_names)?;
            let condition = if loop_.body_on_true {
                condition
            } else if let E::Not { value } = condition {
                *value
            } else {
                E::Not {
                    value: Box::new(condition),
                }
            };
            let condition = cx.expr(&condition)?;
            let header = nodes[block].as_ref().ok_or("missing loop header")?;
            // The pure condition denotes the value after the header's scalar
            // assignments. Keep those assignments before each taken body and
            // once on the final false test, without an artificial break exit.
            result = c_seq(
                result,
                c_seq(
                    c_while(condition, Vec::new(), c_seq(header.clone(), body)),
                    header.clone(),
                ),
            );
            block = loop_.exit;
            continue;
        }
        result = c_seq(
            result,
            nodes[block].as_ref().ok_or("missing MIR block")?.clone(),
        );
        match &mir.blocks[block].terminator {
            T::If {
                condition,
                then_target,
                else_target,
            } => {
                let join = if flow.joins[block] == mir.blocks.len() {
                    stop
                } else {
                    flow.joins[block]
                };
                let yes = region(cx, mir, nodes, flow, emitted, *then_target, join)?;
                let no = region(cx, mir, nodes, flow, emitted, *else_target, join)?;
                result = c_seq(result, c_if(cx.expr(condition)?, yes, no));
                block = join;
            }
            T::Goto { target } | T::Drop { target, .. } | T::Call { target, .. } => block = *target,
            _ => break,
        }
    }
    Ok(result)
}

fn accesses(expressions: &[&E], live: &BTreeMap<&str, String>) -> CStatement {
    let mut roots = BTreeSet::new();
    let mut pending = expressions.to_vec();
    while let Some(expression) = pending.pop() {
        match expression {
            E::Local { name } => {
                if let Some(flag) = live.get(name.as_str()) {
                    roots.insert(flag.as_str());
                }
            }
            E::Binary { left, right, .. } => {
                pending.push(left);
                pending.push(right);
            }
            E::Index { slice, index } => {
                pending.push(slice);
                pending.push(index);
            }
            E::Array { elements } => pending.extend(elements),
            E::Repeat { value, .. } => pending.push(value),
            E::Not { value }
            | E::BitwiseNot { value, .. }
            | E::Cast { value, .. }
            | E::IntegerFrom { value, .. } => pending.push(value),
            E::Borrow { place, .. } => pending.push(place),
            E::SliceLength { slice } => pending.push(slice),
            E::ArrayToSlice { array, .. } => pending.push(array),
            E::Deref { reference, .. } => pending.push(reference),
            E::Field { base, .. } => pending.push(base),
            E::Call { arguments, .. } => pending.extend(arguments),
            _ => {}
        }
    }
    roots.into_iter().fold(c_skip(), |s, flag| {
        c_seq(s, c_assert(c_equal(c_variable(flag), c_int32_literal(1))))
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn owned_lowering_does_not_duplicate_unrelated_context() {
        use crate::languages::rust::schema::{Field, Place, Span};
        fn count(s: &CStatement) -> usize {
            match s {
                CStatement::Seq(a, b) => 1 + count(a) + count(b),
                CStatement::If {
                    then_branch,
                    else_branch,
                    ..
                } => 1 + count(then_branch) + count(else_branch),
                _ => 1,
            }
        }
        let span = Span { line: 1, column: 1 };
        let record = Record {
            name: "Live".into(),
            size: 4,
            alignment: 4,
            fields: vec![Field {
                name: "x".into(),
                offset: 0,
                value_type: Type::I32,
            }],
            destructor: None,
        };
        let owned = Function {
            name: "owned".into(),
            return_type: Type::Unit,
            parameters: vec![],
            body: vec![],
            span: span.clone(),
            mir: Some(MirBody {
                locals: vec![Place {
                    name: "value".into(),
                    value_type: Type::Record {
                        name: "Live".into(),
                    },
                    span: span.clone(),
                }],
                blocks: vec![crate::languages::rust::schema::MirBlock {
                    statements: vec![S::Initialize {
                        target: "value".into(),
                        record: "Live".into(),
                        fields: vec![E::Integer { value: 3 }],
                    }],
                    terminator: T::Return,
                }],
            }),
        };
        let mut baseline = None;
        for size in [8, 32, 128] {
            let mut export = RustExport {
                schema: 2,
                compiler_commit: String::new(),
                target: String::new(),
                edition: "2024".into(),
                overflow_checks: true,
                panic: "abort".into(),
                mir_opt_level: 0,
                logical_source: "scale.rs".into(),
                records: vec![record.clone()],
                functions: vec![owned.clone()],
            };
            for i in 0..size {
                let mut unrelated = record.clone();
                unrelated.name = format!("Unrelated{i}");
                export.records.push(unrelated);
                export.functions.push(Function {
                    name: format!("unrelated{i}"),
                    return_type: Type::I32,
                    parameters: vec![],
                    body: vec![super::super::S::Return {
                        value: Some(E::Integer { value: 0 }),
                    }],
                    mir: None,
                    span: span.clone(),
                });
            }
            let (lowered, _) = super::super::lower(&export).unwrap();
            assert_eq!(lowered.len(), size + 1);
            let operations = count(lowered[0].to_kernel_function().body());
            assert_eq!(*baseline.get_or_insert(operations), operations);
        }
    }
    #[test]
    fn diamond_cleanup_joins_emit_each_block_once_at_multiple_sizes() {
        for count in [8, 32, 128] {
            let mut blocks = Vec::new();
            for i in 0..count {
                let start = i * 3;
                blocks.push(crate::languages::rust::schema::MirBlock {
                    statements: vec![],
                    terminator: T::If {
                        condition: E::Boolean { value: true },
                        then_target: start + 1,
                        else_target: start + 2,
                    },
                });
                for _ in 0..2 {
                    blocks.push(crate::languages::rust::schema::MirBlock {
                        statements: vec![],
                        terminator: T::Goto { target: start + 3 },
                    });
                }
            }
            blocks.push(crate::languages::rust::schema::MirBlock {
                statements: vec![],
                terminator: T::Return,
            });
            let mir = MirBody {
                locals: vec![],
                blocks,
            };
            let order = (0..mir.blocks.len()).rev().collect::<Vec<_>>();
            let joins = postdominators(&mir, &order);
            for i in 0..count {
                assert_eq!(joins[i * 3], i * 3 + 3);
            }
            let fields = BTreeMap::new();
            let layouts = BTreeMap::new();
            let records = BTreeMap::new();
            let functions = BTreeMap::new();
            let mut cx = Context {
                chunk_iterators: BTreeSet::new(),
                local_arrays: BTreeSet::new(),
                arrays: BTreeMap::new(),
                owned_locals: BTreeSet::new(),
                slices: BTreeMap::new(),
                source: "scale.rs",
                function: "scale",
                fields: &fields,
                next_load: 0,
                next_temporary: 0,
                locals: BTreeSet::new(),
                return_type: C0Type::Void,
                layouts: &layouts,
                records: &records,
                functions: &functions,
            };
            let nodes = (0..mir.blocks.len())
                .map(|i| Some(c_assert(c_int32_literal(i as u32))))
                .collect::<Vec<_>>();
            let mut emitted = vec![false; mir.blocks.len()];
            let structured = region(
                &mut cx,
                &mir,
                &nodes,
                &flow::Flow {
                    order,
                    joins,
                    loops: BTreeMap::new(),
                    scalar_names: BTreeSet::new(),
                },
                &mut emitted,
                0,
                mir.blocks.len(),
            )
            .unwrap();
            assert!(emitted.iter().all(|b| *b));
            fn assertions(s: &CStatement) -> usize {
                match s {
                    CStatement::Seq(a, b) => assertions(a) + assertions(b),
                    CStatement::If {
                        then_branch,
                        else_branch,
                        ..
                    } => assertions(then_branch) + assertions(else_branch),
                    CStatement::Assert { .. } => 1,
                    _ => 0,
                }
            }
            assert_eq!(assertions(&structured), count * 3 + 1);
        }
    }
}
