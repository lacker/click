use super::*;
use crate::kernel::CheckedPopulationMemberExchange;
use crate::kernel::ResourceDescription;
#[cfg(test)]
use crate::kernel::binary_node;
use crate::kernel::population_authority::storage_creation::is_external_population_anchor;
use crate::kernel::{CheckedPopulationAuthorityExchange, ExecutionValue};
use crate::kernel::{CompareRelation, OverflowOperation};
use crate::kernel::{MachineCastSpelling, cast_term};
use crate::kernel::{binary_term, unary_term};
use crate::kernel::{
    bits32_constant, constant_i64, constant_u32, constant_u64, int32_constant, int64_constant,
    native_constant, uint32_constant, uint64_constant,
};
use std::fmt::Write;

fn memory_havoc_write_set_identity(mutable_ranges: &[MemoryRange]) -> String {
    let mut ranges = mutable_ranges
        .iter()
        .map(havoc_range_identity)
        .collect::<Vec<_>>();
    ranges.sort();
    let mut identity = format!("write-set:{};", ranges.len());
    for range in ranges {
        let _ = write!(identity, "{}:", range.len());
        identity.push_str(&range);
    }
    identity
}

enum HavocIdentityTask {
    Text(&'static str),
    Pointer(Address),
    PointerOffset(AddressOffset),
    Bitvector(OldMachineTerm),
    Condition(OldConditionTerm),
    FloatCondition {
        condition: FloatCondition,
        is_float64: bool,
    },
    LeaveRegisteredLoad(Variable),
}

fn write_havoc_string(identity: &mut String, tag: &str, value: &str) {
    let _ = write!(identity, "{tag}{}:", value.len());
    identity.push_str(value);
}

fn write_havoc_block(identity: &mut String, block: AddressBase) {
    match block {
        AddressBase::SliceLength { slice, instance } => {
            if let Some(parameter) = slice.parameter() {
                write_havoc_string(identity, "bslice", parameter);
            } else if let Some(local) = slice.local() {
                write_havoc_string(identity, "bslocal", &local.canonical().to_string());
            }
            let _ = write!(identity, "{instance:?};");
        }
        AddressBase::ReferenceCarrier { referent, instance } => {
            identity.push_str("bref;");
            write_havoc_block(
                identity,
                SymbolicMemory::local_pointer(referent.as_ref())
                    .base
                    .clone(),
            );
            let _ = write!(identity, "{instance:?};");
        }
        AddressBase::AggregateReturn { frame } => {
            let _ = write!(identity, "breturn{frame};");
        }
        AddressBase::ContractResult => identity.push_str("br;"),
        AddressBase::ContractException => identity.push_str("bexception;"),
        AddressBase::StaticObject { binding } => {
            write_havoc_string(identity, "bst", &binding.to_string())
        }
        AddressBase::AutomaticLocal { binding, instance } => {
            write_havoc_string(identity, "bl", &binding.to_string());
            let _ = write!(identity, "{instance:?};");
        }
        AddressBase::PureFunctionApplication(application) => {
            let _ = write!(identity, "bpure{};", application.id());
        }
        AddressBase::Concrete(name) => write_havoc_string(identity, "bc", &name),
        AddressBase::StringLiteral {
            identity: name,
            bytes,
        } => {
            write_havoc_string(identity, "bsl", &name.to_string());
            let _ = write!(identity, "{}:", bytes.len());
            for byte in bytes {
                let _ = write!(identity, "{byte:02x}");
            }
            identity.push(';');
        }
        AddressBase::Function(name) => write_havoc_string(identity, "bf", &name),
        AddressBase::FunctionSymbolic(variable) => {
            let _ = write!(identity, "bfs{};", variable.0);
        }
        AddressBase::ExternalArgument => identity.push_str("be;"),
        AddressBase::ExternalObject(variable) => {
            let _ = write!(identity, "beo{};", variable.0);
        }
        AddressBase::Symbolic(variable) => {
            let _ = write!(identity, "bs{};", variable.0);
        }
        AddressBase::Load(load) => {
            let _ = write!(identity, "blp{};", load.id());
        }
        AddressBase::SliceData(load) => {
            let _ = write!(identity, "bls{};", load.id());
        }
        AddressBase::Heap(value) => {
            let _ = write!(identity, "bh{value};");
        }
        AddressBase::Temporary(value) => {
            let _ = write!(identity, "bt{value};");
        }
    }
}

fn push_registered_load(
    identity: &mut String,
    tasks: &mut Vec<HavocIdentityTask>,
    active_loads: &mut BTreeSet<Variable>,
    variable: Variable,
) -> bool {
    let Some((_, pointer)) = crate::kernel::eval::registered_load_for_variable(&variable) else {
        return false;
    };
    if !active_loads.insert(variable) {
        let _ = write!(identity, "recursive-load:{};", variable.0);
        return true;
    }
    identity.push_str("load(");
    tasks.push(HavocIdentityTask::LeaveRegisteredLoad(variable));
    tasks.push(HavocIdentityTask::Text(")"));
    tasks.push(HavocIdentityTask::Pointer(pointer));
    true
}

/// The havoc-identity tag of a format-carrying binary node, the one each
/// per-width operator node had before the nodes were merged.
fn havoc_machine_binary_tag(format: MachineIntegerType, op: MachineBinaryOp) -> &'static str {
    use MachineBinaryOp as Op;
    let signed = format != MachineIntegerType::UInt64;
    match (signed, op) {
        (true, Op::Add) => "ti64a",
        (true, Op::Subtract) => "ti64s",
        (true, Op::Multiply) => "ti64m",
        (true, Op::Divide) => "ti64d",
        (true, Op::Remainder) => "ti64r",
        (true, Op::ShiftLeft) => "ti64l",
        (true, Op::ShiftRight) => "ti64ar",
        (true, Op::BitwiseAnd) => "ti64ba",
        (true, Op::BitwiseOr) => "ti64bo",
        (true, Op::BitwiseXor) => "ti64bx",
        (false, Op::Add) => "tu64a",
        (false, Op::Subtract) => "tu64s",
        (false, Op::Multiply) => "tu64m",
        (false, Op::Divide) => "tu64d",
        (false, Op::Remainder) => "tu64r",
        (false, Op::ShiftLeft) => "tu64l",
        (false, Op::ShiftRight) => "tu64lr",
        (false, Op::BitwiseAnd) => "tu64ba",
        (false, Op::BitwiseOr) => "tu64bo",
        (false, Op::BitwiseXor) => "tu64bx",
    }
}

fn push_havoc_binary(
    identity: &mut String,
    tasks: &mut Vec<HavocIdentityTask>,
    tag: &'static str,
    left: OldMachineTerm,
    right: OldMachineTerm,
) {
    identity.push_str(tag);
    identity.push('(');
    tasks.push(HavocIdentityTask::Text(")"));
    tasks.push(HavocIdentityTask::Bitvector(right));
    tasks.push(HavocIdentityTask::Text(","));
    tasks.push(HavocIdentityTask::Bitvector(left));
}

/// Pushes a machine comparison or overflow test: its format, relation or
/// operation, and its operands.
fn push_havoc_comparison(
    identity: &mut String,
    tasks: &mut Vec<HavocIdentityTask>,
    op: BitvectorComparisonOp,
    left: OldMachineTerm,
    right: OldMachineTerm,
) {
    use CompareRelation as R;
    use MachineIntegerType as Ty;
    use OverflowOperation as O;
    let tag = match op {
        BitvectorComparisonOp::Compare(Ty::Int32, R::LessThan) => "clt",
        BitvectorComparisonOp::Compare(Ty::Int32, R::LessEqual) => "cle",
        BitvectorComparisonOp::Compare(Ty::Int32, R::GreaterThan) => "cgt",
        BitvectorComparisonOp::Compare(Ty::Int32, R::GreaterEqual) => "cge",
        BitvectorComparisonOp::Compare(Ty::Int32 | Ty::UInt32, R::Equal) => "ceq",
        BitvectorComparisonOp::Overflows(Ty::Int32, O::Add) => "cao",
        BitvectorComparisonOp::Overflows(Ty::Int32, O::Subtract) => "cso",
        BitvectorComparisonOp::Overflows(Ty::Int32, O::Multiply) => "cmo",
        BitvectorComparisonOp::Overflows(Ty::Int32, O::Divide) => "cdo",
        BitvectorComparisonOp::Overflows(Ty::Int32, O::ShiftLeft) => "clo",
        BitvectorComparisonOp::Compare(Ty::Int64, R::LessThan) => "ci64lt",
        BitvectorComparisonOp::Compare(Ty::Int64, R::LessEqual) => "ci64le",
        BitvectorComparisonOp::Compare(Ty::Int64, R::GreaterThan) => "ci64gt",
        BitvectorComparisonOp::Compare(Ty::Int64, R::GreaterEqual) => "ci64ge",
        BitvectorComparisonOp::Compare(Ty::UInt64, R::LessThan) => "cu64lt",
        BitvectorComparisonOp::Compare(Ty::UInt64, R::LessEqual) => "cu64le",
        BitvectorComparisonOp::Compare(Ty::UInt64, R::GreaterThan) => "cu64gt",
        BitvectorComparisonOp::Compare(Ty::UInt64, R::GreaterEqual) => "cu64ge",
        BitvectorComparisonOp::Compare(Ty::Int64, R::Equal) => "c64eq",
        BitvectorComparisonOp::Overflows(Ty::Int64, O::Add) => "ci64ao",
        BitvectorComparisonOp::Overflows(Ty::Int64, O::Subtract) => "ci64so",
        BitvectorComparisonOp::Overflows(Ty::Int64, O::Multiply) => "ci64mo",
        BitvectorComparisonOp::Overflows(Ty::Int64, O::Divide) => "ci64do",
        BitvectorComparisonOp::Overflows(Ty::Int64, O::ShiftLeft) => "ci64lo",
        // Every other format spells its name with the relation or operation.
        other => {
            let kind = if other.is_overflow() { "o" } else { "c" };
            let _ = write!(
                identity,
                "c{}{kind}{}",
                other.format().name(),
                other.program_symbol()
            );
            ""
        }
    };
    push_havoc_binary(identity, tasks, tag, left, right);
}

fn havoc_range_identity(range: &MemoryRange) -> String {
    // Keep traversal on an explicit stack so a valid deeply nested footprint
    // cannot overflow Rust's call stack. Strings are length-delimited where
    // their contents are unconstrained; fixed tags delimit every other node.
    // Registered load variables normally form an acyclic generation history,
    // but encode an exact variable back-edge if a malformed cycle appears.
    // The bounds are encoded as the terms they are. One untyped term can
    // bound a range of either index kind, so the kind is in the tag.
    let (start, end) = range.bound_terms();
    write_havoc_identity(
        String::from(if range.wide_bounds().is_some() {
            "wide-range("
        } else {
            "range("
        }),
        vec![
            HavocIdentityTask::Text(")"),
            HavocIdentityTask::Bitvector(OldMachineTerm::constant(range.element_width())),
            HavocIdentityTask::Text(","),
            HavocIdentityTask::Bitvector(end.clone()),
            HavocIdentityTask::Text(","),
            HavocIdentityTask::Bitvector(start.clone()),
            HavocIdentityTask::Text(","),
            HavocIdentityTask::Pointer(range.base().clone()),
        ],
    )
}

/// The structural key of one condition premise, in the havoc identity
/// encoding.
fn havoc_condition_identity(condition: &OldConditionTerm, value: bool) -> String {
    write_havoc_identity(
        format!("condition{value}("),
        vec![
            HavocIdentityTask::Text(")"),
            HavocIdentityTask::Condition(condition.clone()),
        ],
    )
}

/// Runs the havoc identity encoding of `tasks` (a stack, last task first)
/// onto `identity`.
fn write_havoc_identity(mut identity: String, mut tasks: Vec<HavocIdentityTask>) -> String {
    let mut active_loads = BTreeSet::new();
    while let Some(task) = tasks.pop() {
        match task {
            HavocIdentityTask::Text(text) => identity.push_str(text),
            HavocIdentityTask::LeaveRegisteredLoad(variable) => {
                active_loads.remove(&variable);
            }
            HavocIdentityTask::Pointer(pointer) => {
                crate::instrumentation::record_deterministic_work(1);
                identity.push_str("pointer(");
                write_havoc_block(&mut identity, pointer.base.clone());
                identity.push(',');
                tasks.push(HavocIdentityTask::Text(")"));
                tasks.push(HavocIdentityTask::PointerOffset(pointer.offset.clone()));
            }
            HavocIdentityTask::PointerOffset(offset) => {
                crate::instrumentation::record_deterministic_work(1);
                let offset = match offset.into_add() {
                    Ok((left, right)) => {
                        identity.push_str("oa(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::PointerOffset(right));
                        tasks.push(HavocIdentityTask::Text(","));
                        tasks.push(HavocIdentityTask::PointerOffset(left));
                        continue;
                    }
                    Err(offset) => offset,
                };
                match offset.view() {
                    OffsetView::Constant(value) => {
                        let _ = write!(identity, "oc{value};");
                    }
                    OffsetView::Variable(variable) => {
                        if !push_registered_load(
                            &mut identity,
                            &mut tasks,
                            &mut active_loads,
                            variable,
                        ) {
                            let _ = write!(identity, "ov{};", variable.0);
                        }
                    }
                    OffsetView::Add(..) => unreachable!("sums are split above"),
                    OffsetView::Int32Scaled { index, byte_width }
                    | OffsetView::Int64Scaled {
                        index, byte_width, ..
                    } => {
                        identity.push_str("os(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::PointerOffset(AddressOffset::constant(
                            byte_width,
                        )));
                        tasks.push(HavocIdentityTask::Text(","));
                        tasks.push(HavocIdentityTask::Bitvector(
                            index.structural_value().clone(),
                        ));
                    }
                }
            }
            HavocIdentityTask::Bitvector(term) => {
                crate::instrumentation::record_deterministic_work(1);
                match term {
                    OldMachineTerm::ThreadHandle(id) => {
                        let _ = write!(identity, "thread-handle:{id:?};");
                    }
                    OldMachineTerm::PureApplicationCount(application) => {
                        let _ = write!(identity, "tpcount{};", application.id());
                    }
                    OldMachineTerm::Cast {
                        spelling: MachineCastSpelling::Generic,
                        value,
                        from: source,
                        to: destination,
                    } => {
                        let _ = write!(identity, "tmcast{source:?}:{destination:?}(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Bitvector(value.as_ref().clone()));
                    }

                    native_constant!(format, bits) => {
                        let _ = write!(identity, "twc{:?}:{:032x};", format.format(), bits);
                    }

                    int32_constant!(value) => {
                        let _ = write!(identity, "tc{value};", value = constant_u32(value));
                    }
                    uint32_constant!(value) => {
                        let _ = write!(identity, "tuc{value};", value = constant_u32(value));
                    }
                    int64_constant!(value) => {
                        let _ = write!(identity, "ti64c{value};", value = constant_i64(value));
                    }
                    uint64_constant!(value) => {
                        let _ = write!(identity, "tu64c{value};", value = constant_u64(value));
                    }
                    OldMachineTerm::Variable(variable) => {
                        if !push_registered_load(
                            &mut identity,
                            &mut tasks,
                            &mut active_loads,
                            variable,
                        ) {
                            let _ = write!(identity, "tv{};", variable.0);
                        }
                    }
                    binary_term!(Int32, Add, left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "ta", *left, *right)
                    }
                    binary_term!(Int32, Subtract, left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "ts", *left, *right)
                    }
                    binary_term!(Int32, Multiply, left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tm", *left, *right)
                    }
                    binary_term!(Int32, Divide, left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "td", *left, *right)
                    }
                    binary_term!(UInt32, Divide, left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tud", *left, *right)
                    }
                    binary_term!(Int32, Remainder, left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tr", *left, *right)
                    }
                    binary_term!(UInt32, Remainder, left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tur", *left, *right)
                    }
                    binary_term!(Int32, ShiftLeft, left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tl", *left, *right)
                    }
                    binary_term!(Int32, ShiftRight, left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tar", *left, *right)
                    }
                    binary_term!(UInt32, ShiftRight, left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tlr", *left, *right)
                    }
                    binary_term!(Int32, BitwiseAnd, left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tba", *left, *right)
                    }
                    binary_term!(Int32, BitwiseOr, left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tbo", *left, *right)
                    }
                    binary_term!(Int32, BitwiseXor, left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tbx", *left, *right)
                    }
                    unary_term!(Int32, BitwiseNot, value) => {
                        identity.push_str("tbn(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Bitvector(value.as_ref().clone()));
                    }
                    OldMachineTerm::Float32Negate(value) => {
                        identity.push_str("tf32n(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Bitvector(value.as_ref().clone()));
                    }
                    OldMachineTerm::Float64Negate(value) => {
                        identity.push_str("tf64n(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Bitvector(value.as_ref().clone()));
                    }
                    OldMachineTerm::Float32Binary {
                        operator,
                        left,
                        right,
                    } => {
                        let tag = match operator {
                            FloatBinaryOperator::Add => "tf32a",
                            FloatBinaryOperator::Subtract => "tf32s",
                            FloatBinaryOperator::Multiply => "tf32m",
                            FloatBinaryOperator::Divide => "tf32d",
                        };
                        push_havoc_binary(&mut identity, &mut tasks, tag, *left, *right);
                    }
                    OldMachineTerm::Float64Binary {
                        operator,
                        left,
                        right,
                    } => {
                        let tag = match operator {
                            FloatBinaryOperator::Add => "tf64a",
                            FloatBinaryOperator::Subtract => "tf64s",
                            FloatBinaryOperator::Multiply => "tf64m",
                            FloatBinaryOperator::Divide => "tf64d",
                        };
                        push_havoc_binary(&mut identity, &mut tasks, tag, *left, *right);
                    }
                    cast_term!(Int64From32, value) => push_havoc_binary(
                        &mut identity,
                        &mut tasks,
                        "ti64f32",
                        *value.clone(),
                        *value,
                    ),
                    cast_term!(UInt64From32, value) => push_havoc_binary(
                        &mut identity,
                        &mut tasks,
                        "tu64f32",
                        *value.clone(),
                        *value,
                    ),
                    cast_term!(UInt32From64, value) => push_havoc_binary(
                        &mut identity,
                        &mut tasks,
                        "tu32f64",
                        *value.clone(),
                        *value,
                    ),
                    cast_term!(Int64FromUInt32, value) => push_havoc_binary(
                        &mut identity,
                        &mut tasks,
                        "ti64fu32",
                        *value.clone(),
                        *value,
                    ),
                    cast_term!(UInt64FromInt32, value) => push_havoc_binary(
                        &mut identity,
                        &mut tasks,
                        "tu64fi32",
                        *value.clone(),
                        *value,
                    ),
                    cast_term!(UInt64FromInt64, value) => push_havoc_binary(
                        &mut identity,
                        &mut tasks,
                        "tu64fi64",
                        *value.clone(),
                        *value,
                    ),
                    OldMachineTerm::Unary {
                        format,
                        op: MachineUnaryOp::BitwiseNot,
                        operand,
                    } => {
                        identity.push_str(match format {
                            MachineIntegerType::UInt64 => "tu64bn(",
                            _ => "ti64bn(",
                        });
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Bitvector(*operand));
                    }
                    OldMachineTerm::Binary {
                        format,
                        op,
                        left,
                        right,
                    } => push_havoc_binary(
                        &mut identity,
                        &mut tasks,
                        havoc_machine_binary_tag(format, op),
                        *left,
                        *right,
                    ),
                    OldMachineTerm::BoolCast { to, value } => {
                        let _ = write!(identity, "tbcast{to:?}(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Condition(*value));
                    }
                    OldMachineTerm::If {
                        condition,
                        then_term,
                        else_term,
                    } => {
                        identity.push_str("ti(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Bitvector(*else_term));
                        tasks.push(HavocIdentityTask::Text(","));
                        tasks.push(HavocIdentityTask::Bitvector(*then_term));
                        tasks.push(HavocIdentityTask::Text(","));
                        tasks.push(HavocIdentityTask::Condition(*condition));
                    }
                    OldMachineTerm::RangeFold {
                        start,
                        end,
                        initial,
                        accumulator,
                        item,
                        body,
                    } => {
                        let _ = write!(identity, "tf({};{};", accumulator.0, item.0);
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Bitvector(*body));
                        tasks.push(HavocIdentityTask::Text(","));
                        tasks.push(HavocIdentityTask::Bitvector(*initial));
                        tasks.push(HavocIdentityTask::Text(","));
                        tasks.push(HavocIdentityTask::Bitvector(*end));
                        tasks.push(HavocIdentityTask::Text(","));
                        tasks.push(HavocIdentityTask::Bitvector(*start));
                    }
                    OldMachineTerm::PureFunctionApplication { name, arguments } => {
                        identity.push_str("tp(");
                        write_havoc_string(&mut identity, "n", &name);
                        tasks.push(HavocIdentityTask::Text(")"));
                        for (index, argument) in arguments.into_iter().enumerate().rev() {
                            tasks.push(HavocIdentityTask::Bitvector(argument));
                            if index > 0 {
                                tasks.push(HavocIdentityTask::Text(","));
                            }
                        }
                    }
                    OldMachineTerm::ClickFunctionApplication { .. }
                    | OldMachineTerm::AlgebraicMatch { .. }
                    | OldMachineTerm::IntegerToMachine { .. } => {
                        use std::hash::{Hash, Hasher};
                        let mut hasher = std::collections::hash_map::DefaultHasher::new();
                        term.hash(&mut hasher);
                        let _ = write!(identity, "click:{:x};", hasher.finish());
                    }
                    OldMachineTerm::MemoryLoad(_, pointer, kind) => {
                        let _ = write!(identity, "load:{kind:?}(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Pointer(pointer.into()));
                    }
                    OldMachineTerm::IntegerAddress(pointer, _) => {
                        identity.push_str("address(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Pointer(*pointer));
                    }
                }
            }
            HavocIdentityTask::FloatCondition {
                condition,
                is_float64,
            } => {
                crate::instrumentation::record_deterministic_work(1);
                let width = if is_float64 { "64" } else { "32" };
                match condition {
                    FloatCondition::Comparison {
                        operator,
                        left,
                        right,
                    } => {
                        let _ = write!(identity, "fc{width}cmp{operator:?}(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Bitvector(*right));
                        tasks.push(HavocIdentityTask::Text(","));
                        tasks.push(HavocIdentityTask::Bitvector(*left));
                    }
                    FloatCondition::Classification {
                        classification,
                        value,
                    } => {
                        let _ = write!(identity, "fc{width}class{classification:?}(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Bitvector(value.as_ref().clone()));
                    }
                }
            }
            HavocIdentityTask::Condition(condition) => {
                crate::instrumentation::record_deterministic_work(1);
                match condition {
                    OldConditionTerm::PointerEqual(left, right) => {
                        let _ = write!(identity, "pveq({left:?},{right:?});");
                    }

                    OldConditionTerm::AlgebraicEqual(left, right) => {
                        let _ = write!(identity, "aeq({left:?},{right:?});");
                    }
                    OldConditionTerm::Constant(value) => {
                        let _ = write!(identity, "cc{value};");
                    }
                    OldConditionTerm::Variable(variable) => {
                        let _ = write!(identity, "cv{};", variable.0);
                    }
                    OldConditionTerm::Compare {
                        format,
                        relation,
                        left,
                        right,
                    } => push_havoc_comparison(
                        &mut identity,
                        &mut tasks,
                        BitvectorComparisonOp::Compare(format, relation),
                        *left,
                        *right,
                    ),
                    OldConditionTerm::Overflows {
                        format,
                        op,
                        left,
                        right,
                    } => push_havoc_comparison(
                        &mut identity,
                        &mut tasks,
                        BitvectorComparisonOp::Overflows(format, op),
                        *left,
                        *right,
                    ),
                    crate::kernel::integer_comparison_condition!(_, _) => {
                        let _ = write!(identity, "icond{condition:?};");
                    }
                    OldConditionTerm::Float32(condition) => {
                        tasks.push(HavocIdentityTask::FloatCondition {
                            condition,
                            is_float64: false,
                        });
                    }
                    OldConditionTerm::Float64(condition) => {
                        tasks.push(HavocIdentityTask::FloatCondition {
                            condition,
                            is_float64: true,
                        });
                    }
                    OldConditionTerm::AddressOffsetEqual(left, right) => {
                        identity.push_str("coe(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::PointerOffset(*right));
                        tasks.push(HavocIdentityTask::Text(","));
                        tasks.push(HavocIdentityTask::PointerOffset(*left));
                    }
                    OldConditionTerm::AddressEqual(left, right) => {
                        identity.push_str("cpe(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Pointer(*right));
                        tasks.push(HavocIdentityTask::Text(","));
                        tasks.push(HavocIdentityTask::Pointer(*left));
                    }
                    // As a word-valued Click application: by its hash.
                    OldConditionTerm::BoolApplication(application) => {
                        use std::hash::{Hash, Hasher};
                        let mut hasher = std::collections::hash_map::DefaultHasher::new();
                        application.hash(&mut hasher);
                        let _ = write!(identity, "bclick:{:x};", hasher.finish());
                    }
                    OldConditionTerm::BoolIf {
                        condition,
                        then_condition,
                        else_condition,
                    } => {
                        identity.push_str("bif(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Condition(*else_condition));
                        tasks.push(HavocIdentityTask::Text(","));
                        tasks.push(HavocIdentityTask::Condition(*then_condition));
                        tasks.push(HavocIdentityTask::Text(","));
                        tasks.push(HavocIdentityTask::Condition(*condition));
                    }
                    OldConditionTerm::BoolEqual(left, right) => {
                        identity.push_str("beq(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Condition(*right));
                        tasks.push(HavocIdentityTask::Text(","));
                        tasks.push(HavocIdentityTask::Condition(*left));
                    }
                }
            }
        }
    }
    identity
}

#[cfg(test)]
mod call_havoc_local_retention_tests {
    use super::*;

    #[test]
    fn call_havoc_drops_explicitly_written_local_fields_and_keeps_disjoint_cells() {
        let block: AddressBase = "local:borrowed-guard".into();
        let at = |offset| Address::new(block.clone(), AddressOffset::constant(offset));
        let before = SymbolicMemory::new()
            .with_block(block.clone(), 16)
            .store(at(0), ProgramValue::Int32(OldMachineTerm::constant(7)))
            .store(at(8), ProgramValue::Int32(OldMachineTerm::constant(1)))
            .store(at(12), ProgramValue::Int32(OldMachineTerm::constant(9)));
        let range = MemoryRange::new_with_element_width(at(8), 0u32.into(), 4u32.into(), 1);
        let facts = PureFactContext::new();
        let after = before.clone().with_call_memory_havoc(
            Variable(944_012),
            std::slice::from_ref(&range),
            &facts,
            None,
        );
        assert_eq!(
            after.known_value(&at(8)),
            None,
            "a callee can write directly named local storage"
        );
        assert_eq!(after.known_value(&at(0)), before.known_value(&at(0)));
        assert_eq!(after.known_value(&at(12)), before.known_value(&at(12)));
        assert!(after.matches_call_memory_havoc_result(
            &before,
            std::slice::from_ref(&range),
            &facts,
            None
        ));
        let stale = after
            .clone()
            .store(at(8), ProgramValue::Int32(OldMachineTerm::constant(1)));
        assert!(!stale.matches_call_memory_havoc_result(
            &before,
            std::slice::from_ref(&range),
            &facts,
            None
        ));
    }

    #[test]
    fn call_havoc_preserves_only_existing_local_initialization() {
        let at = |offset| {
            Address::new(
                "local:initialization".into(),
                AddressOffset::constant(offset),
            )
        };
        let before = SymbolicMemory::new()
            .with_block(at(0).base.clone(), 16)
            .store(at(0), ProgramValue::Int32(OldMachineTerm::constant(7)));
        let range = MemoryRange::new_with_element_width(at(0), 0u32.into(), 16u32.into(), 1);
        let facts = PureFactContext::new();
        let after = before.clone().with_call_memory_havoc(
            Variable(944_015),
            std::slice::from_ref(&range),
            &facts,
            None,
        );
        assert!(after.has_initialized_bytes_at(&at(0), 4));
        assert!(!after.has_initialized_bytes_at(&at(0), 8));
        assert!(!after.has_initialized_bytes_at(&at(8), 4));
        let named = after.clone().materialize_named_cell(
            at(0),
            ProgramValue::Int32(OldMachineTerm::Variable(Variable(944_016))),
        );
        assert!(
            named.known_value(&at(0)).is_none(),
            "logical naming does not materialize automatic storage"
        );
        assert!(named.has_initialized_bytes_at(&at(0), 4));
        let fresh = after
            .clone()
            .materialize_named_cell(at(8), ProgramValue::Int32(OldMachineTerm::constant(1)));
        assert!(fresh.known_value(&at(8)).is_none());
        let mut forged = after.clone();
        std::sync::Arc::make_mut(&mut forged.heap)
            .initialized
            .record(&at(8), 4);
        assert!(!forged.matches_call_memory_havoc_result(
            &before,
            std::slice::from_ref(&range),
            &facts,
            None
        ));
        let mut widened = after.clone();
        std::sync::Arc::make_mut(&mut widened.heap)
            .initialized
            .record(&at(0), 8);
        assert!(!widened.matches_call_memory_havoc_result(
            &before,
            std::slice::from_ref(&range),
            &facts,
            None
        ));
        let retired = after.without_local_block(&at(0).base);
        assert!(!retired.has_initialized_bytes_at(&at(0), 4));
        assert!(!retired.is_loadable_concretely(&at(0), 4));
    }

    #[test]
    fn call_havoc_drops_explicitly_written_local_union_views() {
        let pointer = Address::new("local:borrowed-union".into(), AddressOffset::constant(0));
        let before = SymbolicMemory::new()
            .with_block(pointer.base.clone(), 8)
            .store_union_views(
                pointer.clone(),
                8,
                vec![(
                    pointer.clone(),
                    ProgramType::Int32,
                    ProgramValue::Int32(OldMachineTerm::constant(1)),
                )],
            );
        let range =
            MemoryRange::new_with_element_width(pointer.clone(), 0u32.into(), 4u32.into(), 1);
        let facts = PureFactContext::new();
        let after = before.clone().with_call_memory_havoc(
            Variable(944_013),
            std::slice::from_ref(&range),
            &facts,
            None,
        );
        assert_eq!(after.known_union_value(&pointer, ProgramType::Int32), None);
        assert!(after.matches_call_memory_havoc_result(
            &before,
            std::slice::from_ref(&range),
            &facts,
            None
        ));
    }

    #[test]
    fn call_havoc_drops_a_local_cell_written_through_an_interior_alias() {
        let pointer = Address::new("local:interior-field".into(), AddressOffset::constant(0));
        let alias = Address::symbolic(Variable(944_021));
        let before = SymbolicMemory::new()
            .with_block(pointer.base.clone(), 4)
            .store(
                pointer.clone(),
                ProgramValue::Int32(OldMachineTerm::constant(7)),
            );
        let facts = PureFactContext::new().assume_condition(
            OldConditionTerm::address_equal(alias.clone(), pointer.offset_by_bytes(1)),
            true,
        );
        let range = MemoryRange::new_with_element_width(alias, 0u32.into(), 1u32.into(), 1);
        let after = before.clone().with_call_memory_havoc(
            Variable(944_022),
            std::slice::from_ref(&range),
            &facts,
            None,
        );
        assert!(after.known_value(&pointer).is_none());
        assert!(after.has_initialized_bytes_at(&pointer, 4));
        assert!(after.matches_call_memory_havoc_result(
            &before,
            std::slice::from_ref(&range),
            &facts,
            None
        ));
        assert!(
            !after
                .store(pointer, ProgramValue::Int32(OldMachineTerm::constant(7)))
                .matches_call_memory_havoc_result(
                    &before,
                    std::slice::from_ref(&range),
                    &facts,
                    None
                )
        );
    }

    #[test]
    fn call_havoc_drops_local_cell_when_write_range_is_assumed_equal_to_it() {
        let local = Address::new(
            AddressBase::Concrete("local:t".to_string()),
            AddressOffset::constant(0),
        );
        let symbolic = Address::new(
            AddressBase::Symbolic(Variable(944_001)),
            AddressOffset::constant(0),
        );
        let assumed_alias_range = MemoryRange::new(
            symbolic.clone(),
            OldMachineTerm::constant(0),
            OldMachineTerm::constant(1),
        );
        let assumptions = PureFactContext::new().assume_proposition(Proposition::condition_is(
            OldConditionTerm::address_equal(symbolic, local.clone()),
            true,
        ));
        let unrelated_range = MemoryRange::new(
            Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0)),
            OldMachineTerm::constant(0),
            OldMachineTerm::constant(1),
        );
        let value = ProgramValue::Int32(OldMachineTerm::constant(41));
        let before = SymbolicMemory::new()
            .with_block(local.base.clone(), 4)
            .store(local.clone(), value.clone());

        let retained = before.clone().with_call_memory_havoc(
            Variable(944_010),
            std::slice::from_ref(&unrelated_range),
            &PureFactContext::new(),
            None,
        );
        assert_eq!(retained.known_value(&local), Some(value));

        let havocked = before.clone().with_call_memory_havoc(
            Variable(944_011),
            std::slice::from_ref(&assumed_alias_range),
            &assumptions,
            None,
        );
        assert_eq!(
            havocked.known_value(&local),
            None,
            "an assumed-equal write range must invalidate the local cell"
        );
        assert!(havocked.matches_call_memory_havoc_result(
            &before,
            std::slice::from_ref(&assumed_alias_range),
            &assumptions,
            None,
        ));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/primitives/memory_state/call_havoc_local_retention_tests.rs"
        );
    }
}

#[cfg(test)]
mod call_havoc_union_view_tests {
    use super::*;

    /// A call havoc drops a typed union view inside its write set exactly as
    /// it drops a cell, keeps one it cannot reach, and its checker accepts
    /// that result and refuses the one that keeps the written view.
    #[test]
    fn call_havoc_drops_union_views_in_its_write_set_and_the_checker_agrees() {
        let block: AddressBase = "global:union-havoc".into();
        let written = Address::new(block.clone(), AddressOffset::constant(0));
        let sibling = Address::new(block.clone(), AddressOffset::constant(8));
        let view = |pointer: &Address, value: u32| {
            (
                pointer.clone(),
                ProgramType::Int32,
                ProgramValue::Int32(OldMachineTerm::constant(value)),
            )
        };
        let before = SymbolicMemory::new()
            .with_block(block, 16)
            .store_union_views(written.clone(), 8, vec![view(&written, 3)])
            .store_union_views(sibling.clone(), 8, vec![view(&sibling, 5)]);
        let range = MemoryRange::new_with_element_width(
            written.clone(),
            OldMachineTerm::constant(0),
            OldMachineTerm::constant(4),
            1,
        );
        let assumptions = PureFactContext::new();
        let after = before.clone().with_call_memory_havoc(
            Variable(944_020),
            std::slice::from_ref(&range),
            &assumptions,
            None,
        );
        assert_eq!(after.known_union_value(&written, ProgramType::Int32), None);
        assert_eq!(
            after.known_union_value(&sibling, ProgramType::Int32),
            Some(ProgramValue::Int32(OldMachineTerm::constant(5)))
        );
        assert!(after.matches_call_memory_havoc_result(
            &before,
            std::slice::from_ref(&range),
            &assumptions,
            None,
        ));

        let mut stale = after.clone();
        std::sync::Arc::make_mut(&mut stale.union_cells).insert(
            (written.clone(), ProgramType::Int32),
            ProgramValue::Int32(OldMachineTerm::constant(3)).into(),
        );
        assert!(!stale.matches_call_memory_havoc_result(
            &before,
            std::slice::from_ref(&range),
            &assumptions,
            None,
        ));
    }
}

#[cfg(test)]
mod forget_cached_values_tests {
    use super::*;

    fn int32_view(pointer: &Address, value: u32) -> (Address, ProgramType, ProgramValue) {
        (
            pointer.clone(),
            ProgramType::Int32,
            ProgramValue::Int32(OldMachineTerm::constant(value)),
        )
    }

    fn zeroed_heap_with_cell() -> (SymbolicMemory, Address) {
        let base = Address::new(AddressBase::Heap(944_100), AddressOffset::constant(0));
        let mut memory = SymbolicMemory::new().with_block(base.base.clone(), 8);
        let heap = std::sync::Arc::make_mut(&mut memory.heap);
        heap.live_allocations
            .insert(base.clone(), AllocationSize::int32(8));
        heap.zeroed_allocations.insert(base.clone());
        let memory = memory.store(base.clone(), int32(9));
        (memory, base)
    }

    /// The loop head forgets a typed union view exactly as it forgets a
    /// cell, unless the view's storage is preserved.
    #[test]
    fn loop_havoc_drops_union_views_outside_preserved_blocks() {
        let written = Address::new("global:loop-union".into(), AddressOffset::constant(4));
        let preserved = Address::new("local:loop-union-kept".into(), AddressOffset::constant(4));
        let before = SymbolicMemory::new()
            .with_block(written.base.clone(), 12)
            .with_block(preserved.base.clone(), 12)
            .store_union_views(written.clone(), 8, vec![int32_view(&written, 3)])
            .store_union_views(preserved.clone(), 8, vec![int32_view(&preserved, 5)]);
        let after = before.with_loop_memory_havoc_preserving_borrows(
            Variable(944_101),
            &BTreeSet::from([preserved.base.clone()]),
            None,
            None,
        );
        assert_eq!(after.known_union_value(&written, ProgramType::Int32), None);
        assert_eq!(
            after.known_union_value(&preserved, ProgramType::Int32),
            Some(ProgramValue::Int32(OldMachineTerm::constant(5)))
        );
    }

    #[test]
    fn indexed_loop_havoc_matches_the_whole_cache_rule() {
        let _session = crate::kernel::VerificationSession::enter();
        let registries = capture_block_registries();
        set_never_address_taken_locals(BTreeSet::from(["private".into()]));
        let state = ExecutionState::new()
            .with_local("private", int32(1))
            .with_local("addressable", int32(2));
        let private = state.locals.slot("private").unwrap().clone();
        let addressable = state.locals.slot("addressable").unwrap().clone();
        let (memory, written) = zeroed_heap_with_cell();
        let memory = memory
            .with_block(private.base.clone(), 4)
            .store(private.clone(), int32(1))
            .with_block(addressable.base.clone(), 4)
            .store(addressable.clone(), int32(2));
        let variable = Variable(944_103);
        let whole = memory.clone().with_loop_memory_havoc_preserving_borrows(
            variable,
            &BTreeSet::from([private.base.clone(), addressable.base.clone()]),
            None,
            None,
        );
        let indexed = memory.clone().with_loop_memory_havoc_preserving_locals(
            variable,
            &state.locals,
            None,
            None,
            None,
        );
        restore_block_registries(&registries);
        assert_eq!(indexed, whole);
        assert_eq!(indexed.known_value(&private), Some(int32(1)));
        assert_eq!(indexed.known_value(&addressable), Some(int32(2)));
        assert_eq!(indexed.known_value(&written), None);
        assert_eq!(memory.known_value(&written), Some(int32(9)));
    }

    /// A zero reading answers for the bytes no cell covers, so the loop
    /// head that forgets a cell written over the zeros forgets the reading
    /// too: otherwise the load after the loop reads zero, not the value.
    #[test]
    fn loop_havoc_drops_the_zero_reading_under_a_forgotten_cell() {
        let (before, base) = zeroed_heap_with_cell();
        let beside = base.with_offset(AddressOffset::constant(4));
        // The cell covers the first four bytes, so only the bytes beside it
        // read as zero.
        assert!(!before.is_zeroed_heap_address(&base, 4, &PureFactContext::new()));
        assert!(before.is_zeroed_heap_address(&beside, 4, &PureFactContext::new()));
        let after = before.with_loop_memory_havoc_preserving_borrows(
            Variable(944_102),
            &BTreeSet::new(),
            None,
            None,
        );
        assert_eq!(after.known_value(&base), None);
        assert!(!after.is_zeroed_heap_address(&beside, 4, &PureFactContext::new()));
    }

    /// A load that covers some byte a cell holds is never answered from the
    /// allocation's zero reading: the cell may start inside the load, start
    /// before it and reach into it, or be a run of slots over it.
    #[test]
    fn a_zero_reading_is_refused_for_bytes_a_cell_covers() {
        let base = Address::new(AddressBase::Heap(944_104), AddressOffset::constant(0));
        let at = |offset: i64| base.with_offset(AddressOffset::constant(offset));
        let mut memory = SymbolicMemory::new().with_block(base.base.clone(), 16);
        let heap = std::sync::Arc::make_mut(&mut memory.heap);
        heap.live_allocations
            .insert(base.clone(), AllocationSize::int32(16));
        heap.zeroed_allocations.insert(base.clone());
        let facts = PureFactContext::new();
        // A byte at offset 5 lies inside the four bytes at 4 and the eight
        // bytes at 0, and beside the four bytes at 8.
        let narrow = memory.clone().store(at(5), uint8(9));
        assert!(!narrow.is_zeroed_heap_address(&at(4), 4, &facts));
        assert!(!narrow.is_zeroed_heap_address(&at(0), 8, &facts));
        assert!(narrow.is_zeroed_heap_address(&at(8), 4, &facts));
        // Eight bytes at 0 contain the four at 4, and miss the four at 8.
        let wide = memory.clone().store(
            at(0),
            ProgramValue::Int64(OldMachineTerm::int64_constant(1 << 40)),
        );
        assert!(!wide.is_zeroed_heap_address(&at(4), 4, &facts));
        assert!(wide.is_zeroed_heap_address(&at(8), 4, &facts));
        // A symbolic offset into a block that holds a cell is not separated
        // from it by any constant.
        let symbolic = base.with_offset(AddressOffset::scaled_int32_node(
            OldMachineTerm::Variable(Variable(944_105)),
            4,
        ));
        assert!(memory.is_zeroed_heap_address(&symbolic, 4, &facts));
        assert!(!narrow.is_zeroed_heap_address(&symbolic, 4, &facts));
    }

    /// An interface join whose arms agree on a zero reading still drops it
    /// when one arm caches a value written over the zeros, and both arms'
    /// abstractions agree on that.
    #[test]
    fn interface_join_drops_a_zero_reading_one_arm_wrote_over() {
        let (wrote, base) = zeroed_heap_with_cell();
        let mut untouched = SymbolicMemory::new().with_block(base.base.clone(), 8);
        let heap = std::sync::Arc::make_mut(&mut untouched.heap);
        heap.live_allocations
            .insert(base.clone(), AllocationSize::int32(8));
        heap.zeroed_allocations.insert(base.clone());
        let arms = [&wrote, &untouched];
        let from_wrote = wrote
            .clone()
            .with_interface_memory_havoc(Variable(944_103), &BTreeSet::new(), &arms)
            .expect("joinable arms");
        let from_untouched = untouched
            .clone()
            .with_interface_memory_havoc(Variable(944_103), &BTreeSet::new(), &arms)
            .expect("joinable arms");
        let beside = base.with_offset(AddressOffset::constant(4));
        assert!(!from_wrote.is_zeroed_heap_address(&beside, 4, &PureFactContext::new()));
        assert_eq!(from_wrote.heap, from_untouched.heap);
    }
}

#[cfg(test)]
mod havoc_identity_tests {
    use super::*;

    fn nested_term(depth: usize, tail: u32) -> OldMachineTerm {
        (0..depth).fold(OldMachineTerm::constant(tail), |term, _| {
            binary_node!(
                Int32,
                Add,
                Box::new(OldMachineTerm::constant(0)),
                Box::new(term)
            )
        })
    }

    fn range(depth: usize, tail: u32) -> MemoryRange {
        MemoryRange::new(
            Address::new("deep-havoc-range".into(), AddressOffset::constant(0)),
            nested_term(depth, tail),
            OldMachineTerm::constant(1_024),
        )
    }

    #[test]
    fn outcome_slot_havoc_identities_are_separate_from_program_storage() {
        let identities = [
            AddressBase::ContractException,
            AddressBase::ContractResult,
            AddressBase::ExternalArgument,
            AddressBase::AggregateReturn { frame: 0 },
            AddressBase::from("local:exception"),
            AddressBase::from("local:__click_exception"),
        ]
        .map(|block| {
            let range = MemoryRange::new(
                Address::new(block, AddressOffset::constant(0)),
                OldMachineTerm::constant(0),
                OldMachineTerm::constant(1),
            );
            memory_havoc_write_set_identity(&[range])
        });
        assert_eq!(
            identities.iter().collect::<BTreeSet<_>>().len(),
            identities.len()
        );
    }

    #[test]
    fn havoc_write_set_identity_distinguishes_terms_below_the_old_depth_limit() {
        let first_range = range(80, 1);
        let second_range = range(80, 2);
        let first_identity = memory_havoc_write_set_identity(std::slice::from_ref(&first_range));
        let second_identity = memory_havoc_write_set_identity(std::slice::from_ref(&second_range));
        assert_ne!(first_identity, second_identity);
        assert!(!first_identity.contains("depth-limit"));
        assert!(!second_identity.contains("depth-limit"));

        let before = SymbolicMemory::new().with_block("deep-havoc-range", 4_096);
        let first = before.clone().with_call_memory_havoc(
            Variable(95_000),
            std::slice::from_ref(&first_range),
            &PureFactContext::new(),
            None,
        );
        let second = before.clone().with_call_memory_havoc(
            Variable(95_000),
            std::slice::from_ref(&second_range),
            &PureFactContext::new(),
            None,
        );
        assert_ne!(
            first, second,
            "distinct deep write sets need distinct endpoints"
        );
        assert!(first.matches_call_memory_havoc_result(
            &before,
            std::slice::from_ref(&first_range),
            &PureFactContext::new(),
            None,
        ));
        assert!(!first.matches_call_memory_havoc_result(
            &before,
            std::slice::from_ref(&second_range),
            &PureFactContext::new(),
            None,
        ));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/primitives/memory_state/havoc_identity_tests.rs");
    }
}

fn memory_havoc_write_set_fingerprint(mutable_ranges: &[MemoryRange]) -> u32 {
    use std::hash::{Hash, Hasher};

    // This compact marker fingerprint remains form-invariant across proof
    // execution and independent certification. Call havocs supplement it with
    // a lossless structural key below; loop markers retain this shape because
    // their checked write set is already carried by the derivation edge.
    let mut shape = mutable_ranges
        .iter()
        .map(|range| {
            (
                format!("{:?}", range.base().base),
                range.constant_start(),
                range.constant_end(),
            )
        })
        .collect::<Vec<_>>();
    shape.sort();
    let mut hasher = std::hash::DefaultHasher::new();
    shape.hash(&mut hasher);
    (hasher.finish() as u32) | 1
}

/// Whether a held resource grants read authority over a symbolic byte span
/// at `base`.
///
/// The trusted graph/index selects a sole footprint or start supplier. The
/// ordinary read-core coverage judgment converts byte and element coordinates
/// and checks quantity and bounds. Unknown or ambiguous selection refuses;
/// this consumer must never search the resource input for a successful check.
pub(crate) fn resource_context_has_symbolic_range_read(
    resources: &ResourceContext,
    base: &Address,
    bytes: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    let footprint =
        MemoryRange::new_with_element_width(base.clone(), 0u32.into(), bytes.clone(), 1);
    resources
        .symbolic_range_read_supported(&footprint, assumptions, None)
        .unwrap_or(false)
}

impl LocalEnvironment {
    pub(crate) fn resolve_binding(&self, name: &BindingName) -> BindingName {
        if let Some(place) = name.unresolved_slice_length() {
            crate::instrumentation::record_deterministic_work(1);
            if let Some((_, BindingName::Local(id))) = self
                .visible_names
                .get(place)
                .and_then(|entries| entries.last())
            {
                return BindingName::lexical_local_slice_length(id, true);
            }
            return BindingName::slice_length(place);
        }
        if matches!(name, BindingName::ReferenceCarrier(_)) {
            crate::instrumentation::record_deterministic_work(1);
        }
        if self.visible_names.is_empty() {
            return name.clone();
        }
        match name {
            BindingName::Named(_)
                if matches!(
                    self.bindings.get(name),
                    Some(LocalBinding::Object {
                        storage_declared: false,
                        ..
                    })
                ) =>
            {
                name.clone()
            }
            BindingName::Named(source) => self
                .visible_names
                .get(source)
                .and_then(|entries| entries.last())
                .map(|(_, binding)| binding.clone())
                .unwrap_or_else(|| name.clone()),
            BindingName::SliceLength(_)
            | BindingName::ReferenceCarrier(_)
            | BindingName::Local(_)
            | BindingName::Static(_)
            | BindingName::ContractResult
            | BindingName::ContractException
            | BindingName::Generated(_) => name.clone(),
        }
    }
    /// The source spelling of this active lexical binding, for source-name
    /// environments. Hidden declarations remain addressable by their typed ID.
    pub(crate) fn active_source_name<'a>(&self, name: &'a BindingName) -> Option<&'a str> {
        let source = match name {
            BindingName::Local(id) => id.spelling()?,
            BindingName::Static(id) => id.spelling(),
            BindingName::Named(name) => name,
            BindingName::SliceLength(_)
            | BindingName::ReferenceCarrier(_)
            | BindingName::ContractResult
            | BindingName::ContractException
            | BindingName::Generated(_) => return None,
        };
        (self.resolve_binding(&BindingName::from(source)) == *name).then_some(source)
    }
    fn index_source_binding(&mut self, name: &BindingName) {
        let BindingName::Local(id) = name else {
            return;
        };
        let Some(source) = id.spelling() else {
            return;
        };
        let mut entries = self.visible_names.get(source).cloned().unwrap_or_default();
        entries.insert(
            (id.scope_depth(), !id.is_parameter(), id.ordinal()),
            name.clone(),
        );
        self.visible_names.insert(source.to_owned(), entries);
    }
    fn unindex_source_binding(&mut self, name: &BindingName) {
        let BindingName::Local(id) = name else {
            return;
        };
        let Some(source) = id.spelling() else {
            return;
        };
        let Some(mut entries) = self.visible_names.get(source).cloned() else {
            return;
        };
        entries.remove(&(id.scope_depth(), !id.is_parameter(), id.ordinal()));
        if entries.is_empty() {
            self.visible_names.remove(&source.to_owned());
        } else {
            self.visible_names.insert(source.to_owned(), entries);
        }
    }

    pub fn new() -> Self {
        Self::default()
    }

    pub fn set(&mut self, name: impl Into<BindingName>, value: ProgramValue) {
        let name = self.resolve_binding(&name.into());
        let program_type = value.program_type();
        self.set_typed(name, value, program_type);
    }

    pub fn set_typed(
        &mut self,
        name: impl Into<BindingName>,
        value: ProgramValue,
        program_type: ProgramType,
    ) {
        let name = self.resolve_binding(&name.into());
        self.set_typed_with_qualifiers(name, value, program_type, false, false);
    }

    /// Bind model data independently of any same-named automatic object.
    pub(in crate::kernel) fn bind_logical_typed(
        &mut self,
        name: impl Into<BindingName>,
        value: ProgramValue,
        program_type: ProgramType,
    ) {
        let name = name.into();
        let slot = self
            .bindings
            .get(&name)
            .map(LocalBinding::slot)
            .cloned()
            .unwrap_or_else(|| SymbolicMemory::local_pointer(&name));
        self.insert_binding(
            name,
            LocalBinding::Object {
                storage_declared: false,
                value: value.retag_pointer(program_type).into(),
                program_type,
                slot,
                volatile: false,
                pointee_volatile: false,
                constant: false,
                pointee_constant: false,
            },
        );
    }

    pub(in crate::kernel) fn set_typed_with_qualifiers(
        &mut self,
        name: impl Into<BindingName>,
        value: ProgramValue,
        program_type: ProgramType,
        volatile: bool,
        pointee_volatile: bool,
    ) {
        let name = self.resolve_binding(&name.into());
        self.set_typed_with_all_qualifiers(
            name,
            value,
            program_type,
            volatile,
            pointee_volatile,
            false,
            false,
        );
    }

    pub(in crate::kernel) fn set_typed_with_all_qualifiers(
        &mut self,
        name: impl Into<BindingName>,
        value: ProgramValue,
        program_type: ProgramType,
        volatile: bool,
        pointee_volatile: bool,
        constant: bool,
        pointee_constant: bool,
    ) {
        let name = self.resolve_binding(&name.into());
        let slot = self
            .bindings
            .get(&name)
            .map(LocalBinding::slot)
            .cloned()
            .unwrap_or_else(|| SymbolicMemory::local_pointer(&name));
        self.set_typed_qualified_with_all_qualifiers(
            name,
            value.retag_pointer(program_type),
            program_type,
            slot,
            volatile,
            pointee_volatile,
            constant,
            pointee_constant,
        );
    }

    pub(in crate::kernel) fn set_typed_qualified_with_all_qualifiers(
        &mut self,
        name: impl Into<BindingName>,
        value: ProgramValue,
        program_type: ProgramType,
        slot: Address,
        volatile: bool,
        pointee_volatile: bool,
        constant: bool,
        pointee_constant: bool,
    ) {
        let name = self.resolve_binding(&name.into());
        let storage_declared = self.bindings.get(&name).is_some_and(|binding| {
            binding.slot() == &slot
                && matches!(
                    binding,
                    LocalBinding::Object {
                        storage_declared: true,
                        ..
                    } | LocalBinding::UninitializedObject { .. }
                )
        });
        self.insert_binding(
            name,
            LocalBinding::Object {
                storage_declared,
                value: value.into(),
                program_type,
                slot,
                volatile,
                pointee_volatile,
                constant,
                pointee_constant,
            },
        );
    }

    pub(in crate::kernel) fn set_global_with_all_qualifiers(
        &mut self,
        name: impl Into<BindingName>,
        program_type: ProgramType,
        slot: Address,
        volatile: bool,
        pointee_volatile: bool,
        constant: bool,
        pointee_constant: bool,
        library_value: Option<StoredExecutionValue>,
    ) {
        let name = self.resolve_binding(&name.into());
        self.insert_binding(
            name,
            LocalBinding::GlobalObject {
                program_type,
                slot,
                volatile,
                pointee_volatile,
                constant,
                pointee_constant,
                library_value,
            },
        );
    }

    pub(in crate::kernel) fn set_uninitialized_with_all_qualifiers(
        &mut self,
        name: impl Into<BindingName>,
        program_type: ProgramType,
        slot: Address,
        volatile: bool,
        pointee_volatile: bool,
        constant: bool,
        pointee_constant: bool,
    ) {
        let name = self.resolve_binding(&name.into());
        self.insert_binding(
            name,
            LocalBinding::UninitializedObject {
                program_type,
                slot,
                volatile,
                pointee_volatile,
                constant,
                pointee_constant,
            },
        );
    }

    #[cfg(test)]
    pub(in crate::kernel) fn set_array_object_at(
        &mut self,
        name: impl Into<BindingName>,
        element_type: ProgramType,
        length: u32,
        slot: Address,
    ) {
        let name = self.resolve_binding(&name.into());
        self.set_array_object_at_with_constant(name, element_type, length, slot, false);
    }

    pub(in crate::kernel) fn set_array_object_at_with_constant(
        &mut self,
        name: impl Into<BindingName>,
        element_type: ProgramType,
        length: u32,
        slot: Address,
        constant: bool,
    ) {
        let name = self.resolve_binding(&name.into());
        self.insert_binding(
            name,
            LocalBinding::ArrayObject {
                element_type,
                length,
                slot,
                constant,
            },
        );
    }

    pub(in crate::kernel) fn set_aggregate_object_at(
        &mut self,
        name: impl Into<BindingName>,
        layout: AggregateLayout,
        slot: Address,
    ) {
        let name = self.resolve_binding(&name.into());
        self.set_aggregate_object_at_with_constant(name, layout, slot, false);
    }

    pub(in crate::kernel) fn set_aggregate_object_at_with_constant(
        &mut self,
        name: impl Into<BindingName>,
        layout: AggregateLayout,
        slot: Address,
        constant: bool,
    ) {
        let name = self.resolve_binding(&name.into());
        self.insert_binding(
            name,
            LocalBinding::AggregateObject {
                layout,
                slot,
                constant,
                proof_input_for: None,
            },
        );
    }

    pub(in crate::kernel) fn set_retained_typed_with_all_qualifiers(
        &mut self,
        name: impl Into<BindingName>,
        value: impl Into<StoredExecutionValue>,
        program_type: ProgramType,
        volatile: bool,
        pointee_volatile: bool,
        constant: bool,
        pointee_constant: bool,
    ) {
        let value = value.into();
        if value.shared().is_none() {
            self.set_typed_with_all_qualifiers(
                name,
                value.into_native(),
                program_type,
                volatile,
                pointee_volatile,
                constant,
                pointee_constant,
            );
            return;
        }
        let value = if value.program_type().is_pointer() {
            value.into_value().with_pointer_binding(program_type).into()
        } else {
            value
        };
        let name = self.resolve_binding(&name.into());
        let slot = self
            .bindings
            .get(&name)
            .map(LocalBinding::slot)
            .cloned()
            .unwrap_or_else(|| SymbolicMemory::local_pointer(&name));
        self.set_retained_typed_qualified_with_all_qualifiers(
            name,
            value,
            program_type,
            slot,
            volatile,
            pointee_volatile,
            constant,
            pointee_constant,
        );
    }

    pub(in crate::kernel) fn set_retained_typed_qualified_with_all_qualifiers(
        &mut self,
        name: impl Into<BindingName>,
        value: impl Into<StoredExecutionValue>,
        program_type: ProgramType,
        slot: Address,
        volatile: bool,
        pointee_volatile: bool,
        constant: bool,
        pointee_constant: bool,
    ) {
        let value = value.into();
        if value.shared().is_none() {
            self.set_typed_qualified_with_all_qualifiers(
                name,
                value.into_native(),
                program_type,
                slot,
                volatile,
                pointee_volatile,
                constant,
                pointee_constant,
            );
            return;
        }
        let value_type = value.program_type();
        let value = if value_type.is_pointer() {
            value.into_value().with_pointer_binding(value_type).into()
        } else {
            value
        };
        let name = self.resolve_binding(&name.into());
        let storage_declared = self.bindings.get(&name).is_some_and(|binding| {
            binding.slot() == &slot
                && matches!(
                    binding,
                    LocalBinding::Object {
                        storage_declared: true,
                        ..
                    } | LocalBinding::UninitializedObject { .. }
                )
        });
        self.insert_binding(
            name,
            LocalBinding::Object {
                storage_declared,
                value,
                program_type,
                slot,
                volatile,
                pointee_volatile,
                constant,
                pointee_constant,
            },
        );
    }

    /// Borrow the exact retained value. Use `get_native` only at a native output boundary.
    pub fn get(&self, name: impl Into<BindingName>) -> Option<&StoredExecutionValue> {
        let name = self.resolve_binding(&name.into());
        match self.bindings.get(&name) {
            Some(LocalBinding::Object { value, .. }) => Some(value),
            Some(LocalBinding::UninitializedObject { .. })
            | Some(LocalBinding::GlobalObject { .. })
            | Some(LocalBinding::ArrayObject { .. })
            | Some(LocalBinding::AggregateObject { .. })
            | None => None,
        }
    }

    pub(crate) fn nonvolatile_scalar(
        &self,
        name: &BindingName,
        expected_type: ProgramType,
    ) -> Option<&StoredExecutionValue> {
        match self.binding(name)? {
            LocalBinding::Object {
                value,
                program_type,
                volatile: false,
                ..
            } if *program_type == expected_type => Some(value),
            _ => None,
        }
    }

    /// Explicit legacy output: reconstruct one selected native value, without caching it.
    pub fn get_native(
        &self,
        name: impl Into<BindingName>,
    ) -> Option<std::borrow::Cow<'_, ProgramValue>> {
        let name = self.resolve_binding(&name.into());
        self.get(&name).map(|value| value.native())
    }

    /// Read one automatic array's metadata by name without scanning the frame.
    pub fn array_object_element_type(&self, name: impl Into<BindingName>) -> Option<ProgramType> {
        let name = self.resolve_binding(&name.into());
        match self.bindings.get(&name) {
            Some(LocalBinding::ArrayObject { element_type, .. }) => Some(*element_type),
            _ => None,
        }
    }

    /// Exact name membership, including arrays and uninitialized objects.
    /// Proof-local binders use this indexed query to reject shadowing without
    /// materializing or scanning the complete local environment.
    pub fn contains_name(&self, name: impl Into<BindingName>) -> bool {
        let name = self.resolve_binding(&name.into());
        self.bindings.contains_key(&name)
    }

    /// Whether this frame has bound anything at all.
    ///
    /// A frame that has bound nothing owns no automatic object and no
    /// parameter pseudo-slot, so nothing it holds can collide with a name a
    /// frame it calls declares. That is the question an entering frame asks,
    /// and asking it this way keeps the answer a single indexed check rather
    /// than a walk of the caller's environment.
    pub(in crate::kernel) fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }

    /// Whether this name is a declared automatic object whose value the
    /// execution has not produced yet. Reading it has no defined path, so a
    /// proposition that names it cannot lower; a diagnostic uses this to name
    /// the local instead of reporting a path count.
    pub fn is_uninitialized_object(&self, name: impl Into<BindingName>) -> bool {
        let name = self.resolve_binding(&name.into());
        matches!(
            self.bindings.get(&name),
            Some(LocalBinding::UninitializedObject { .. })
        )
    }

    /// Iterate values without expanding shared expression payloads.
    pub fn object_values(&self) -> impl Iterator<Item = (&BindingName, &StoredExecutionValue)> {
        self.bindings
            .iter()
            .filter_map(|(name, binding)| match binding {
                LocalBinding::Object { value, .. } => Some((name, value)),
                LocalBinding::UninitializedObject { .. }
                | LocalBinding::GlobalObject { .. }
                | LocalBinding::ArrayObject { .. }
                | LocalBinding::AggregateObject { .. } => None,
            })
    }

    pub fn aggregate_object_values(
        &self,
    ) -> impl Iterator<Item = (&BindingName, &AggregateLayout, &Address)> + '_ {
        self.bindings
            .iter()
            .filter_map(|(name, binding)| match binding {
                LocalBinding::AggregateObject { layout, slot, .. } => Some((name, layout, slot)),
                LocalBinding::Object { .. }
                | LocalBinding::UninitializedObject { .. }
                | LocalBinding::GlobalObject { .. }
                | LocalBinding::ArrayObject { .. } => None,
            })
    }

    /// The type of the value local `name`'s object holds, and the object's
    /// address, for a local that keeps one value in memory
    /// ([`AggregateLayout::holding_value`]).
    pub fn held_value_local(
        &self,
        name: impl Into<BindingName>,
    ) -> Option<(ProgramType, &Address)> {
        let name = self.resolve_binding(&name.into());
        match self.bindings.get(&name)? {
            LocalBinding::AggregateObject { layout, slot, .. } => {
                Some((layout.value_type()?, slot))
            }
            _ => None,
        }
    }

    /// The locals that keep one value in memory, with the value's type and
    /// the object's address.
    pub fn held_value_locals(
        &self,
    ) -> impl Iterator<Item = (&BindingName, ProgramType, &Address)> + '_ {
        self.aggregate_object_values()
            .filter_map(|(name, layout, slot)| Some((name, layout.value_type()?, slot)))
    }

    /// Read one local array's pointer and element type without scanning the frame.
    /// `None` for an array whose elements have no pointer type of their own,
    /// as [`Self::array_object_values`] leaves it out.
    pub fn array_object_value(
        &self,
        name: impl Into<BindingName>,
    ) -> Option<(ProgramValue, ProgramType)> {
        let name = self.resolve_binding(&name.into());
        let LocalBinding::ArrayObject {
            element_type, slot, ..
        } = self.bindings.get(&name)?
        else {
            return None;
        };
        Some((
            ProgramValue::typed_pointer(slot.clone(), element_type.pointer_to()?),
            *element_type,
        ))
    }

    /// Each local array as a pointer to its first element, with the element
    /// type. An array whose elements have no pointer type of their own, such
    /// as `const char *const *t[]`, has no such pointer value and is left
    /// out: a proof cannot name it, though execution reads it.
    pub fn array_object_values(
        &self,
    ) -> impl Iterator<Item = (&BindingName, ProgramValue, ProgramType)> + '_ {
        self.bindings
            .iter()
            .filter_map(|(name, binding)| match binding {
                LocalBinding::ArrayObject {
                    element_type, slot, ..
                } => Some((
                    name,
                    ProgramValue::typed_pointer(slot.clone(), element_type.pointer_to()?),
                    *element_type,
                )),
                LocalBinding::Object { .. }
                | LocalBinding::UninitializedObject { .. }
                | LocalBinding::GlobalObject { .. }
                | LocalBinding::AggregateObject { .. } => None,
            })
    }

    pub(in crate::kernel) fn object_type(
        &self,
        name: impl Into<BindingName>,
    ) -> Option<ProgramType> {
        let name = self.resolve_binding(&name.into());
        match self.binding(&name) {
            Some(LocalBinding::Object { program_type, .. }) => Some(*program_type),
            Some(LocalBinding::UninitializedObject { program_type, .. }) => Some(*program_type),
            Some(LocalBinding::GlobalObject { program_type, .. }) => Some(*program_type),
            Some(LocalBinding::ArrayObject { element_type, .. }) => Some(*element_type),
            None => None,
            Some(LocalBinding::AggregateObject { .. }) => None,
        }
    }

    pub(crate) fn scalar_object_type(&self, name: impl Into<BindingName>) -> Option<ProgramType> {
        let name = self.resolve_binding(&name.into());
        match self.binding(&name) {
            Some(LocalBinding::Object { program_type, .. }) => Some(*program_type),
            Some(LocalBinding::UninitializedObject { program_type, .. }) => Some(*program_type),
            Some(LocalBinding::GlobalObject { .. }) => None,
            Some(LocalBinding::ArrayObject { .. })
            | Some(LocalBinding::AggregateObject { .. })
            | None => None,
        }
    }

    pub(in crate::kernel) fn binding(&self, name: impl Into<BindingName>) -> Option<&LocalBinding> {
        let name = self.resolve_binding(&name.into());
        self.bindings.get(&name)
    }

    pub(in crate::kernel) fn slot(&self, name: impl Into<BindingName>) -> Option<&Address> {
        let name = self.resolve_binding(&name.into());
        self.binding(&name).map(LocalBinding::slot)
    }

    pub(in crate::kernel) fn slots(&self) -> impl Iterator<Item = &Address> {
        self.slots.keys()
    }

    pub(in crate::kernel) fn automatic_slots(&self) -> impl Iterator<Item = &Address> {
        self.automatic_slots.keys()
    }

    pub(in crate::kernel) fn has_slot_in_block(&self, block: &AddressBase) -> bool {
        let first = Address::new(block.clone(), AddressOffset::constant(i64::MIN));
        self.slots.contains_key(&first)
            || self
                .slots
                .get_greater_than(&first)
                .is_some_and(|(slot, _)| &slot.base == block)
    }

    pub(in crate::kernel) fn is_proof_input_slot(&self, slot: &Address) -> bool {
        self.name_for_slot(slot).is_some_and(|name| {
            matches!(
                self.bindings.get(name),
                Some(LocalBinding::AggregateObject {
                    proof_input_for: Some(_),
                    ..
                })
            )
        })
    }

    pub(crate) fn name_for_slot(&self, pointer: &Address) -> Option<&BindingName> {
        self.slots.get(pointer)
    }

    /// The array objects whose slots lie in `block`, with their element
    /// types and slots, found through the slot index as
    /// [`Self::names_with_slot_in`] finds them.
    pub(crate) fn array_objects_with_slot_in(
        &self,
        block: &AddressBase,
    ) -> Vec<(&BindingName, ProgramType, &Address)> {
        self.names_with_slot_in(block)
            .into_iter()
            .filter_map(|name| match self.binding(name)? {
                LocalBinding::ArrayObject {
                    element_type, slot, ..
                } => Some((name, *element_type, slot)),
                _ => None,
            })
            .collect()
    }

    /// The names whose slots lie in `block`, found through the slot index:
    /// pointers order by block first, so they are one run of slot keys.
    pub(in crate::kernel) fn names_with_slot_in(&self, block: &AddressBase) -> Vec<&BindingName> {
        let mut names = Vec::new();
        let mut at = Address::new(block.clone(), AddressOffset::constant(i64::MIN));
        if let Some(name) = self.slots.get(&at) {
            names.push(name);
        }
        while let Some((pointer, name)) = self.slots.get_greater_than(&at) {
            if &pointer.base != block {
                break;
            }
            names.push(name);
            at = pointer.clone();
        }
        names
    }

    /// The names bound differently in `self` and `other`, or bound in one
    /// only, in ascending order. Bindings the two frames share are skipped
    /// by identity, so frames derived from one another cost their changes.
    pub(in crate::kernel) fn differing_names<'a>(
        &'a self,
        other: &'a Self,
    ) -> impl Iterator<Item = &'a BindingName> + 'a {
        self.bindings.diff(&other.bindings).map(|(name, _, _)| {
            crate::instrumentation::record_deterministic_work(1);
            name
        })
    }

    pub(in crate::kernel) fn is_array_object(&self, name: impl Into<BindingName>) -> bool {
        let name = self.resolve_binding(&name.into());
        matches!(self.binding(&name), Some(LocalBinding::ArrayObject { .. }))
    }

    pub(in crate::kernel) fn is_global_object(&self, name: impl Into<BindingName>) -> bool {
        let name = self.resolve_binding(&name.into());
        matches!(self.binding(&name), Some(LocalBinding::GlobalObject { .. }))
    }

    pub(in crate::kernel) fn is_aggregate_object(&self, name: impl Into<BindingName>) -> bool {
        let name = self.resolve_binding(&name.into());
        matches!(
            self.binding(&name),
            Some(LocalBinding::AggregateObject { .. })
        )
    }

    pub(crate) fn aggregate_object_pointer(
        &self,
        name: impl Into<BindingName>,
    ) -> Option<&Address> {
        let name = self.resolve_binding(&name.into());
        match self.binding(&name) {
            Some(LocalBinding::AggregateObject { slot, .. }) => Some(slot),
            _ => None,
        }
    }

    pub(crate) fn aggregate_layout(
        &self,
        name: impl Into<BindingName>,
    ) -> Option<&AggregateLayout> {
        let name = self.resolve_binding(&name.into());
        match self.binding(&name) {
            Some(LocalBinding::AggregateObject { layout, .. }) => Some(layout),
            _ => None,
        }
    }
}

impl LocalBinding {
    pub(in crate::kernel) fn slot(&self) -> &Address {
        match self {
            Self::Object { slot, .. }
            | Self::UninitializedObject { slot, .. }
            | Self::GlobalObject { slot, .. }
            | Self::ArrayObject { slot, .. }
            | Self::AggregateObject { slot, .. } => slot,
        }
    }
}

fn held_address_base(binding: &LocalBinding) -> Option<&AddressBase> {
    let LocalBinding::Object { value, .. } = binding else {
        return None;
    };
    Some(&value.pointer()?.address().base)
}

/// The numeric value of a scalar of integer or truth type.
fn held_integer_term(binding: &LocalBinding) -> Option<&OldMachineTerm> {
    let LocalBinding::Object { value, .. } = binding else {
        return None;
    };
    match value.native_payload()?.numeric_value() {
        ProgramValue::Bool(term)
        | ProgramValue::Int8(term)
        | ProgramValue::Int16(term)
        | ProgramValue::Int32(term)
        | ProgramValue::UInt8(term)
        | ProgramValue::UInt16(term)
        | ProgramValue::UInt32(term)
        | ProgramValue::Int64(term)
        | ProgramValue::UInt64(term)
        | ProgramValue::Int128(term)
        | ProgramValue::UInt128(term) => Some(term),
        _ => None,
    }
}

/// The specification value a local of an abstract type holds, when it is a
/// named value: a Rust local holding an enum, a `Vec` or a library iterator.
fn held_algebraic_value(binding: &LocalBinding) -> Option<&AlgebraicTerm> {
    let LocalBinding::Object { value, .. } = binding else {
        return None;
    };
    match value.native_payload()?.numeric_value() {
        ProgramValue::Parameter(term) if matches!(term.node, AlgebraicTermNode::Variable(_)) => {
            Some(term)
        }
        _ => None,
    }
}

/// The fingerprint of a named specification value: its variable's.
fn held_algebraic_fingerprint(term: &AlgebraicTerm) -> Option<u64> {
    use std::hash::{Hash, Hasher};
    let AlgebraicTermNode::Variable(variable) = &term.node else {
        return None;
    };
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    ("algebraic", variable).hash(&mut hasher);
    Some(hasher.finish())
}

/// The index key of what a binding holds: an integer term's fingerprint or
/// a named specification value's. A lookup compares what it finds.
fn held_fingerprint(binding: &LocalBinding) -> Option<u64> {
    if let LocalBinding::Object { value, .. } = binding
        && let Some(root) = value.shared()
    {
        return held_kernel_term_fingerprint(root);
    }
    held_integer_term(binding)
        .map(held_term_fingerprint)
        .or_else(|| held_algebraic_value(binding).and_then(held_algebraic_fingerprint))
}

fn held_term_atom(term: &OldMachineTerm, hasher: &mut impl std::hash::Hasher) {
    use std::hash::Hash;
    std::mem::discriminant(term).hash(hasher);
    // One variant spells every constant, so its format is part of the
    // fingerprint, as the operators' is.
    if let OldMachineTerm::Constant { format, .. } = term {
        format.hash(hasher);
    }
    // So is a conversion's spelling: one variant spells every conversion.
    if let OldMachineTerm::Cast { spelling, .. } = term {
        spelling.hash(hasher);
    }
    match term {
        OldMachineTerm::ThreadHandle(id) => id.hash(hasher),
        OldMachineTerm::Variable(variable) => variable.hash(hasher),
        bits32_constant!(value) => constant_u32(*value).hash(hasher),
        OldMachineTerm::Binary { format, op, .. } => (format, op).hash(hasher),
        OldMachineTerm::Unary { format, op, .. } => (format, op).hash(hasher),
        _ => {}
    }
}

/// A constant-time fingerprint of a term: its root's variant and, for a
/// variable, constant or opaque handle, its payload, and for a format-carrying operator its
/// format and operator, and the same of a binary node's two
/// operands. Equal terms share a fingerprint; a lookup compares the terms
/// it finds, so a shared fingerprint costs only a comparison.
pub(crate) fn held_term_fingerprint(term: &OldMachineTerm) -> u64 {
    use std::hash::Hasher;
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    held_term_atom(term, &mut hasher);
    if let Some((_, left, right)) = term.as_binary() {
        held_term_atom(left, &mut hasher);
        held_term_atom(right, &mut hasher);
    }
    hasher.finish()
}

/// The existing local-name index key, read from common roots and their two
/// immediate binary children. Dummy children supply only a native variant tag;
/// no expression subtree is exported or walked to select the index bucket.
fn held_kernel_term_fingerprint(term: &KernelTerm) -> Option<u64> {
    use std::hash::{Hash, Hasher};
    if matches!(term.ty(), KernelType::Algebraic(_)) {
        let KernelTermNode::Variable(variable) = term.node() else {
            return None;
        };
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        ("algebraic", variable).hash(&mut hasher);
        return Some(hasher.finish());
    }
    fn atom(term: &KernelTerm, hash: &mut impl Hasher) -> Option<()> {
        use KernelTermNode as N;
        let zero = || Box::new(OldMachineTerm::constant(0));
        let shape = match term.node() {
            N::ThreadHandle(id) => OldMachineTerm::ThreadHandle(*id),
            N::MachineLiteral(value) => value.old_term(),
            N::Variable(value) => OldMachineTerm::Variable(*value),
            N::MachineBinary {
                format, operator, ..
            } => OldMachineTerm::Binary {
                format: *format,
                op: *operator,
                left: zero(),
                right: zero(),
            },
            N::MachineUnary {
                format, operator, ..
            } => OldMachineTerm::Unary {
                format: *format,
                op: *operator,
                operand: zero(),
            },
            N::MachineCast {
                encoding,
                source,
                destination,
                ..
            } => OldMachineTerm::cast_node(*encoding, *source, *destination, *zero()),
            N::BoolCast { destination, .. } => OldMachineTerm::BoolCast {
                to: *destination,
                value: Box::new(OldConditionTerm::Constant(false)),
            },
            N::IntegerToMachine { destination, .. } => OldMachineTerm::IntegerToMachine {
                destination: *destination,
                value: IntegerTerm::constant_i64(0).into(),
            },
            N::Call { .. } => OldMachineTerm::ClickFunctionApplication {
                name: String::new(),
                arguments: Vec::new(),
            },
            N::MachineIf { .. } => OldMachineTerm::If {
                condition: Box::new(OldConditionTerm::Constant(false)),
                then_term: zero(),
                else_term: zero(),
            },
            N::MemoryLoad { .. } => {
                held_term_atom(term.machine_read_leaf()?, hash);
                return Some(());
            }
            N::WrittenMachine(input) => {
                held_term_atom(input.value(), hash);
                return Some(());
            }
            N::MachineObservationInput { observation, .. } => {
                held_term_atom(observation.value(), hash);
                return Some(());
            }
            N::ImportedScalar(input)
                if MachineIntegerType::from_program_type(input.carrier()).is_some() =>
            {
                held_term_atom(input.value(), hash);
                return Some(());
            }
            _ => return None,
        };
        held_term_atom(&shape, hash);
        Some(())
    }
    let mut hash = std::collections::hash_map::DefaultHasher::new();
    atom(term, &mut hash)?;
    if let KernelTermNode::MachineBinary { arguments, .. } = term.node() {
        atom(&arguments[0], &mut hash)?;
        atom(&arguments[1], &mut hash)?;
    }
    Some(hash.finish())
}

fn can_designate_automatic_storage(slot: &Address) -> bool {
    slot.base.is_local_block() && !slot.base.starts_with("local:value-parameter:")
}

impl LocalEnvironment {
    /// An environment of these bindings and slots, with its held-term index
    /// built from the bindings.
    pub(in crate::kernel) fn from_parts(
        bindings: crate::persistent::PersistentMap<BindingName, LocalBinding>,
        slots: crate::persistent::PersistentMap<Address, BindingName>,
    ) -> Self {
        let held_terms = bindings
            .iter()
            .filter_map(|(name, binding)| {
                held_fingerprint(binding).map(|fingerprint| ((fingerprint, name.clone()), ()))
            })
            .collect();
        let mut pointer_objects_by_block = crate::persistent::PersistentMap::<
            AddressBase,
            crate::persistent::PersistentMap<BindingName, ()>,
        >::default();
        for (name, binding) in bindings.iter() {
            if let Some(block) = held_address_base(binding) {
                let mut names = pointer_objects_by_block
                    .get(block)
                    .cloned()
                    .unwrap_or_default();
                names.insert(name.clone(), ());
                pointer_objects_by_block.insert(block.clone(), names);
            }
        }
        let automatic_slots = slots
            .keys()
            .filter(|slot| can_designate_automatic_storage(slot))
            .map(|slot| (slot.clone(), ()))
            .collect();
        let mut result = Self {
            bindings,
            slots,
            automatic_slots,
            held_terms,
            pointer_objects_by_block,
            visible_names: Default::default(),
        };
        for (name, _) in result.bindings.clone().iter() {
            result.index_source_binding(name);
        }
        result
    }

    pub(in crate::kernel) fn insert_binding(&mut self, name: BindingName, binding: LocalBinding) {
        if !self.bindings.contains_key(&name) {
            self.index_source_binding(&name);
        }
        let slot = binding.slot().clone();
        let old = self.bindings.get(&name);
        let old_slot = old.map(LocalBinding::slot).cloned();
        let old_held = old.and_then(held_fingerprint);
        let new_held = held_fingerprint(&binding);
        let old_block = old.and_then(held_address_base).cloned();
        let new_block = held_address_base(&binding);
        if old_block.as_ref() != new_block {
            if let Some(block) = old_block.as_ref() {
                self.remove_pointer_object(block, &name);
            }
            if let Some(block) = new_block {
                let mut names = self
                    .pointer_objects_by_block
                    .get(block)
                    .cloned()
                    .unwrap_or_default();
                names.insert(name.clone(), ());
                self.pointer_objects_by_block.insert(block.clone(), names);
            }
        }
        if old_held != new_held {
            if let Some(fingerprint) = old_held {
                self.held_terms.remove(&(fingerprint, name.clone()));
            }
            if let Some(fingerprint) = new_held {
                self.held_terms.insert((fingerprint, name.clone()), ());
            }
        }
        self.bindings.insert(name.clone(), binding);
        if let Some(old_slot) = old_slot
            && old_slot != slot
        {
            self.slots.remove(&old_slot);
            if can_designate_automatic_storage(&old_slot) {
                self.automatic_slots.remove(&old_slot);
            }
        }
        if can_designate_automatic_storage(&slot) && !self.slots.contains_key(&slot) {
            self.automatic_slots.insert(slot.clone(), ());
        }
        self.slots.insert(slot, name);
    }

    fn remove_pointer_object(&mut self, block: &AddressBase, name: impl Into<BindingName>) {
        let name = self.resolve_binding(&name.into());
        let Some(mut names) = self.pointer_objects_by_block.get(block).cloned() else {
            return;
        };
        names.remove(&name.clone());
        if names.is_empty() {
            self.pointer_objects_by_block.remove(block);
        } else {
            self.pointer_objects_by_block.insert(block.clone(), names);
        }
    }

    /// Pointer-valued locals in name order whose held pointers have `block`.
    /// Looking up a spelling visits these candidates, never unrelated locals.
    pub(crate) fn pointer_objects_in_block<'a>(
        &'a self,
        block: &AddressBase,
    ) -> impl Iterator<Item = (&'a BindingName, &'a Pointer)> {
        self.pointer_objects_by_block
            .get(block)
            .into_iter()
            .flat_map(|names| names.iter())
            .map(|(name, ())| {
                let Some(pointer) = self.get(name).and_then(|value| value.pointer()) else {
                    unreachable!("pointer object index follows its binding")
                };
                (name, pointer)
            })
    }

    /// The names, in name order, of the scalar objects holding exactly
    /// `term`: the index narrows the candidates to those sharing its
    /// fingerprint, and each is compared with `term`.
    pub(crate) fn names_holding_integer<'a, 't>(
        &'a self,
        term: &'t OldMachineTerm,
    ) -> impl Iterator<Item = &'a BindingName> + use<'a, 't> {
        self.names_holding_integer_matching(Some(held_term_fingerprint(term)), move |held| {
            if let Some(root) = held.shared() {
                held.machine().is_some_and(|(format, _)| {
                    KernelTermImport::default().machine(format, term) == *root
                })
            } else {
                held.native_payload()
                    .is_some_and(|value| match value.numeric_value() {
                        ProgramValue::Bool(bits) | integer_c_value!(bits) => bits == term,
                        _ => false,
                    })
            }
        })
    }

    /// Name a common arithmetic value using the same indexed candidates as
    /// native spelling. Import only the selected candidate for exact matching.
    pub(crate) fn names_holding_kernel_integer<'a, 't>(
        &'a self,
        term: &'t KernelTerm,
    ) -> impl Iterator<Item = &'a BindingName> + use<'a, 't> {
        self.names_holding_integer_matching(held_kernel_term_fingerprint(term), move |held| {
            let KernelType::Program(ty) = term.ty() else {
                return false;
            };
            let Some(format) = MachineIntegerType::from_program_type(*ty) else {
                return false;
            };
            if let Some(root) = held.shared() {
                root.with_machine_observation_type(format) == *term
            } else {
                held.native_payload()
                    .is_some_and(|value| match value.numeric_value() {
                        ProgramValue::Bool(bits) | integer_c_value!(bits) => {
                            KernelTermImport::default().machine(format, bits) == *term
                        }
                        _ => false,
                    })
            }
        })
    }

    fn names_holding_integer_matching<'a, 't, F: FnMut(&StoredExecutionValue) -> bool + 't>(
        &'a self,
        fingerprint: Option<u64>,
        mut matches: F,
    ) -> impl Iterator<Item = &'a BindingName> + use<'a, 't, F> {
        let mut at =
            fingerprint.map(|fingerprint| (fingerprint, BindingName::Named(String::new())));
        let mut first = true;
        std::iter::from_fn(move || {
            loop {
                let key = at.take()?;
                let next = if first {
                    first = false;
                    match self.held_terms.get_key_value(&key) {
                        Some((found, _)) => Some(found),
                        None => self
                            .held_terms
                            .get_greater_than(&key)
                            .map(|(found, _)| found),
                    }
                } else {
                    self.held_terms
                        .get_greater_than(&key)
                        .map(|(found, _)| found)
                };
                let (found_fingerprint, name) = next?;
                if Some(*found_fingerprint) != fingerprint {
                    return None;
                }
                at = Some((*found_fingerprint, name.clone()));
                crate::instrumentation::record_deterministic_work(1);
                if self
                    .bindings
                    .get(name)
                    .and_then(|binding| match binding {
                        LocalBinding::Object { value, .. } => Some(value),
                        _ => None,
                    })
                    .is_some_and(&mut matches)
                {
                    return Some(name);
                }
            }
        })
    }

    /// The names, in name order, of the objects holding exactly the named
    /// specification value `term`, by the same index.
    pub(crate) fn names_holding_algebraic<'a>(
        &'a self,
        term: &AlgebraicTerm,
    ) -> Vec<&'a BindingName> {
        let Some(fingerprint) = held_algebraic_fingerprint(term) else {
            return Vec::new();
        };
        let mut names = Vec::new();
        let mut at = (fingerprint, BindingName::Named(String::new()));
        let mut entry = self
            .held_terms
            .get_key_value(&at)
            .map(|(found, _)| found)
            .or_else(|| {
                self.held_terms
                    .get_greater_than(&at)
                    .map(|(found, _)| found)
            });
        while let Some((found, name)) = entry {
            if *found != fingerprint {
                break;
            }
            crate::instrumentation::record_deterministic_work(1);
            if self.bindings.get(name).and_then(held_algebraic_value) == Some(term) {
                names.push(name);
            }
            at = (fingerprint, name.clone());
            entry = self
                .held_terms
                .get_greater_than(&at)
                .map(|(found, _)| found);
        }
        names
    }

    /// The scalar objects whose held integer term differs from `earlier`'s,
    /// with the term each holds now: every scalar object when there is no
    /// earlier environment. Shared subtrees are skipped, so for environments
    /// derived from one another the walk visits only the changed bindings.
    pub(crate) fn changed_integer_holdings<'a>(
        &'a self,
        earlier: Option<&'a Self>,
    ) -> Vec<(&'a BindingName, &'a OldMachineTerm)> {
        let changed = |name: &'a BindingName,
                       now: Option<&'a LocalBinding>,
                       before: Option<&LocalBinding>| {
            let held = held_integer_term(now?)?;
            (before.and_then(held_integer_term) != Some(held)).then_some((name, held))
        };
        match earlier {
            Some(earlier) => self
                .bindings
                .diff(&earlier.bindings)
                .filter_map(|(name, now, before)| changed(name, now, before))
                .collect(),
            None => self
                .bindings
                .iter()
                .filter_map(|(name, now)| changed(name, Some(now), None))
                .collect(),
        }
    }

    /// The pointer-valued objects whose held pointer's block differs from
    /// `earlier`'s, with that block: every pointer-valued object when there
    /// is no earlier environment. The walk visits only the changed bindings
    /// of environments derived from one another, as
    /// [`Self::changed_integer_holdings`] does.
    pub(crate) fn changed_address_bases<'a>(
        &'a self,
        earlier: Option<&'a Self>,
    ) -> Vec<(&'a BindingName, &'a AddressBase)> {
        let changed = |name: &'a BindingName,
                       now: Option<&'a LocalBinding>,
                       before: Option<&LocalBinding>| {
            let block = held_address_base(now?)?;
            (before.and_then(held_address_base) != Some(block)).then_some((name, block))
        };
        match earlier {
            Some(earlier) => self
                .bindings
                .diff(&earlier.bindings)
                .filter_map(|(name, now, before)| changed(name, now, before))
                .collect(),
            None => self
                .bindings
                .iter()
                .filter_map(|(name, now)| changed(name, Some(now), None))
                .collect(),
        }
    }

    /// Whether the object `name` holds a pointer into `block`.
    pub(crate) fn holds_pointer_in_block(
        &self,
        name: impl Into<BindingName>,
        block: &AddressBase,
    ) -> bool {
        let name = self.resolve_binding(&name.into());
        self.bindings.get(&name).and_then(held_address_base) == Some(block)
    }

    /// Whether the scalar object `name` holds exactly `term`.
    pub(crate) fn holds_integer(
        &self,
        name: impl Into<BindingName>,
        term: &OldMachineTerm,
    ) -> bool {
        let name = self.resolve_binding(&name.into());
        self.bindings.get(&name).and_then(held_integer_term) == Some(term)
    }

    /// Puts back a binding read from another environment with
    /// [`Self::binding`].
    pub(in crate::kernel) fn restore_binding(
        &mut self,
        name: impl Into<BindingName>,
        binding: LocalBinding,
    ) {
        let name = self.resolve_binding(&name.into());
        self.insert_binding(name.clone(), binding);
    }

    /// Makes an initialized scalar object uninitialized again, keeping its
    /// slot, type and qualifiers, so a read of it is refused. Returns whether
    /// the name held such an object.
    pub(in crate::kernel) fn forget_initialization(
        &mut self,
        name: impl Into<BindingName>,
    ) -> bool {
        let name = self.resolve_binding(&name.into());
        let Some(LocalBinding::Object {
            program_type,
            slot,
            volatile,
            pointee_volatile,
            constant,
            pointee_constant,
            ..
        }) = self.bindings.get(&name).cloned()
        else {
            return false;
        };
        self.insert_binding(
            name.clone(),
            LocalBinding::UninitializedObject {
                program_type,
                slot,
                volatile,
                pointee_volatile,
                constant,
                pointee_constant,
            },
        );
        true
    }

    /// Unbinds one name, as control leaving the scope that declared it does.
    ///
    /// The object's storage is retired separately; this removes the name that
    /// designated it, so a later declaration of that name is a declaration
    /// rather than a re-entry of one this frame still holds.
    pub(in crate::kernel) fn remove(&mut self, name: impl Into<BindingName>) {
        let name = self.resolve_binding(&name.into());
        let Some(binding) = self.bindings.get(&name).cloned() else {
            return;
        };
        if let Some(fingerprint) = held_fingerprint(&binding) {
            self.held_terms.remove(&(fingerprint, name.clone()));
        }
        if let Some(block) = held_address_base(&binding) {
            self.remove_pointer_object(block, &name);
        }
        self.bindings.remove(&name);
        self.unindex_source_binding(&name);
        self.slots.remove(binding.slot());
        if can_designate_automatic_storage(binding.slot()) {
            self.automatic_slots.remove(binding.slot());
        }
    }
}

impl MemoryBlock {
    /// A block of `size` bytes: a 32-bit count, or a symbolic layout's
    /// 64-bit `sizeof`.
    pub fn new(size: impl Into<crate::kernel::LayoutSize>) -> Self {
        Self {
            size: Self::allocation_size_of(size.into()),
            read_only: false,
            declared_scalar_type: None,
            declared_class: None,
        }
    }

    fn allocation_size_of(size: crate::kernel::LayoutSize) -> AllocationSize {
        match size {
            crate::kernel::LayoutSize::Bytes(bytes) => AllocationSize::int32(bytes),
            crate::kernel::LayoutSize::Of(_) => {
                AllocationSize::new(size.term(), crate::kernel::AllocationSizeKind::UInt64)
            }
        }
    }

    pub fn read_only(size: impl Into<crate::kernel::LayoutSize>) -> Self {
        Self {
            size: Self::allocation_size_of(size.into()),
            read_only: true,
            declared_scalar_type: None,
            declared_class: None,
        }
    }

    pub(in crate::kernel) fn with_symbolic_size(size: AllocationSize) -> Self {
        Self {
            size,
            read_only: false,
            declared_scalar_type: None,
            declared_class: None,
        }
    }

    /// The block's byte count. A comparison whose width matters reads it
    /// through [`Self::allocation_size`].
    pub fn size(&self) -> &OldMachineTerm {
        self.size.bytes()
    }

    pub fn allocation_size(&self) -> &AllocationSize {
        &self.size
    }

    pub(in crate::kernel) fn is_read_only(&self) -> bool {
        self.read_only
    }
}

/// The cells [`call_havoc_keeps_cell`] can drop: those in a block not
/// proven distinct from some mutable range's base. Every other cell is kept
/// by the first rung of `range_proven_disjoint_from_pointer`, so the producer
/// and the checker both visit these alone.
fn call_havoc_candidates(mutable_ranges: &[MemoryRange]) -> AliasCandidates {
    AliasCandidates::of_blocks(mutable_ranges.iter().map(|range| &range.base().base))
}

/// The physical bounds of one exact local byte write. These offsets stay
/// within the signed coordinate domain of the per-cell separation rule.
fn call_havoc_exact_byte_write(mutable_ranges: &[MemoryRange]) -> Option<(Address, u32)> {
    use crate::kernel::reasoning::store_gap::{CONSTANT_LIMIT, store_gap_skip_disabled};

    if store_gap_skip_disabled()
        || crate::kernel::assumptions::implicit_consulted_premises_capturing()
        || crate::kernel::assumptions::reasoning_interrupted()
    {
        return None;
    }
    let [range] = mutable_ranges else {
        return None;
    };
    let base = range.base();
    // Byte indexing makes every constant cell offset an exact index in the
    // range's coordinates, including a cell of a different scalar width.
    if !base.base.is_local_block() || range.element_width() != 1 {
        return None;
    }
    let OffsetView::Constant(base_offset) = base.offset.view() else {
        return None;
    };
    let exact = -CONSTANT_LIMIT..=CONSTANT_LIMIT;
    if !exact.contains(&base_offset) {
        return None;
    }
    let start = base_offset + range.signed_constant_start()?;
    let end = base_offset + range.signed_constant_end()?;
    if !exact.contains(&start) || !exact.contains(&end) || end <= start {
        return None;
    }
    let start_pointer = base.with_offset(AddressOffset::constant(start));
    Some((start_pointer, (end - start) as u32))
}

/// The only slots the per-cell rule can reject in a constant-offset local
/// run. Different bases, symbolic offsets and unknown widths need the
/// existing per-slot rule because their byte coordinates may alias.
fn call_havoc_run_window(write: Option<&(Address, u32)>, run: &CellRun) -> Option<(u32, u32)> {
    use crate::kernel::reasoning::memory_resolution::{
        cell_access_byte_width, run_elements_meeting,
    };
    use crate::kernel::reasoning::store_gap::CONSTANT_LIMIT;

    let (pointer, bytes) = write?;
    let (OffsetView::Constant(start), OffsetView::Constant(run_start)) =
        (pointer.offset.view(), run.base().offset.view())
    else {
        return None;
    };
    if pointer.base != run.base().base
        || run.element_width() == 0
        || run.value_width() == 0
        || matches!(run.element_type(), ProgramType::Parameter(_))
        || matches!(run.value_mode(), cell_store::RunValueMode::Constant(value)
            if cell_access_byte_width(value) > run.value_width())
    {
        return None;
    }
    let span =
        i64::from(run.count().checked_sub(1)?).checked_mul(i64::from(run.element_width()))?;
    let exact = -CONSTANT_LIMIT..=CONSTANT_LIMIT;
    if !exact.contains(&run_start) || !exact.contains(&run_start.checked_add(span)?) {
        return None;
    }
    Some(run_elements_meeting(
        run,
        start - run_start,
        i64::from(*bytes),
    ))
}

/// What a caller keeps unchanged across one call: the residual resource context
/// left once the call's consumed and borrowed resources are transferred, the
/// owned memory of that residual's owned instances and folded composites,
/// opened one body layer at the call's entry state, and the opened bodies'
/// own facts, which place a cell spelled through the instance's cells (such
/// as `region->start`) in a range spelled through its fields.
///
/// At the call the transferred and residual resources form one valid
/// composition, and owned memory is exclusive, so a byte an owned residual
/// member holds is disjoint from every byte the callee can own -- and a
/// callee writes only what it owns. Such a cell keeps its value across the
/// call whatever the callee's footprint (an over-approximation of what it
/// owns) covers. The edge records the member that holds it, so a later load
/// can name its pre-call value even when its cached value was dropped.
/// Atomic parameter cells and runs stay cached through the indexed flat
/// partition; other cells are resolved across the recorded edge. A residual
/// view also keeps its bytes: the checked call transfer protects active views
/// from writes. A residual instance that cannot be opened contributes nothing.
/// The body facts hold wherever the instance is held, which is here.
#[derive(Clone, Debug)]
pub(in crate::kernel) struct CallKeptOwnership {
    residual: ResourceContext,
    opened: CallKeptRanges,
    placement: Option<PureFactContext>,
}

/// The kept memory a call havoc records on its edge: owned and viewed ranges,
/// and the condition premises that place a cell in them. See
/// [`MemoryDerivation::CallHavoc`].
#[derive(Clone, Debug)]
pub struct CallKeptRanges {
    ranges: ResourceContext,
    residual: Option<ResourceContext>,
    identity: std::sync::Arc<KeptRangeSet>,
    premises: Vec<(OldConditionTerm, bool)>,
    /// Shared definitions, sorted by name. A query first selects a residual
    /// composite by address, then looks up its definition to open an
    /// argument-direct body ([`Self::range_holding`]).
    direct: Option<std::sync::Arc<[CompositeResourceDefinition]>>,
    /// The caller's composition before transferring call inputs. Its flat
    /// owners exclude unchanged composite owners of the same bytes.
    caller_before_transfer: Option<ResourceContext>,
    /// Residual composite heads absent from that original composition. They
    /// still need checking even inside an original flat owner.
    introduced_composites: ResourceContext,
}

#[derive(Debug)]
struct KeptRangeSet {
    id: u64,
    ranges: HashedOrdMap<MemoryRange, ()>,
    /// The residual's owned composites, with multiplicity, when some of
    /// their ranges are answered per address rather than listed in `ranges`.
    composites: HashedOrdMap<ResourceFact, usize>,
    original_memory: HashedOrdMap<ResourceFact, ()>,
    introduced_composites: HashedOrdMap<ResourceFact, usize>,
    // Share the flat input index, including views, without enumerating it.
    memory_inputs: HashedOrdMap<ResourceFact, ()>,
}

impl PartialEq for CallKeptRanges {
    fn eq(&self, other: &Self) -> bool {
        self.identity.id == other.identity.id && self.premises == other.premises
    }
}
impl Eq for CallKeptRanges {}

fn intern_kept_range_set(
    ranges: HashedOrdMap<MemoryRange, ()>,
    composites: HashedOrdMap<ResourceFact, usize>,
) -> std::sync::Arc<KeptRangeSet> {
    intern_kept_range_set_with_exclusions(
        ranges,
        composites,
        HashedOrdMap::new(),
        HashedOrdMap::new(),
        HashedOrdMap::new(),
    )
}

fn intern_kept_range_set_with_exclusions(
    ranges: HashedOrdMap<MemoryRange, ()>,
    composites: HashedOrdMap<ResourceFact, usize>,
    original_memory: HashedOrdMap<ResourceFact, ()>,
    introduced_composites: HashedOrdMap<ResourceFact, usize>,
    memory_inputs: HashedOrdMap<ResourceFact, ()>,
) -> std::sync::Arc<KeptRangeSet> {
    let mut hash = std::collections::hash_map::DefaultHasher::new();
    std::hash::Hash::hash(&original_memory, &mut hash);
    std::hash::Hash::hash(&introduced_composites, &mut hash);
    std::hash::Hash::hash(&ranges, &mut hash);
    std::hash::Hash::hash(&composites, &mut hash);
    std::hash::Hash::hash(&memory_inputs, &mut hash);
    let hash = std::hash::Hasher::finish(&hash);
    intern_kept_range_set_with_exclusions_and_hash(
        ranges,
        composites,
        original_memory,
        introduced_composites,
        memory_inputs,
        hash,
    )
}

#[cfg(test)]
fn intern_kept_range_set_with_hash(
    ranges: HashedOrdMap<MemoryRange, ()>,
    composites: HashedOrdMap<ResourceFact, usize>,
    hash: u64,
) -> std::sync::Arc<KeptRangeSet> {
    intern_kept_range_set_with_exclusions_and_hash(
        ranges,
        composites,
        HashedOrdMap::new(),
        HashedOrdMap::new(),
        HashedOrdMap::new(),
        hash,
    )
}

fn intern_kept_range_set_with_exclusions_and_hash(
    ranges: HashedOrdMap<MemoryRange, ()>,
    composites: HashedOrdMap<ResourceFact, usize>,
    original_memory: HashedOrdMap<ResourceFact, ()>,
    introduced_composites: HashedOrdMap<ResourceFact, usize>,
    memory_inputs: HashedOrdMap<ResourceFact, ()>,
    hash: u64,
) -> std::sync::Arc<KeptRangeSet> {
    type Buckets = std::collections::HashMap<u64, Vec<std::sync::Weak<KeptRangeSet>>>;
    static SETS: std::sync::OnceLock<std::sync::Mutex<Buckets>> = std::sync::OnceLock::new();
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
    let mut sets = SETS
        .get_or_init(Default::default)
        .lock()
        .expect("kept range sets");
    let bucket = sets.entry(hash).or_default();
    bucket.retain(|candidate| candidate.strong_count() != 0);
    for candidate in bucket.iter().filter_map(std::sync::Weak::upgrade) {
        let same = |left: bool, diff: &mut dyn Iterator<Item = ()>| left || diff.next().is_none();
        if same(
            candidate.ranges.ptr_eq(&ranges),
            &mut candidate.ranges.diff(&ranges).map(|_| ()),
        ) && same(
            candidate.composites.ptr_eq(&composites),
            &mut candidate.composites.diff(&composites).map(|_| ()),
        ) && same(
            candidate.original_memory.ptr_eq(&original_memory),
            &mut candidate.original_memory.diff(&original_memory).map(|_| ()),
        ) && same(
            candidate
                .introduced_composites
                .ptr_eq(&introduced_composites),
            &mut candidate
                .introduced_composites
                .diff(&introduced_composites)
                .map(|_| ()),
        ) && same(
            candidate.memory_inputs.ptr_eq(&memory_inputs),
            &mut candidate.memory_inputs.diff(&memory_inputs).map(|_| ()),
        ) {
            return candidate;
        }
    }
    let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    assert!(id != u64::MAX, "kept range identity space exhausted");
    let result = std::sync::Arc::new(KeptRangeSet {
        id,
        ranges,
        composites,
        original_memory,
        introduced_composites,
        memory_inputs,
    });
    bucket.push(std::sync::Arc::downgrade(&result));
    result
}

#[cfg(test)]
thread_local! {
    static KEPT_CALL_RANGE_QUERIES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

impl CallKeptRanges {
    #[cfg(test)]
    pub(crate) fn take_range_queries() -> usize {
        KEPT_CALL_RANGE_QUERIES.with(|queries| queries.replace(0))
    }

    pub(in crate::kernel) fn new(
        ranges: ResourceContext,
        premises: Vec<(OldConditionTerm, bool)>,
        direct: Option<std::sync::Arc<[CompositeResourceDefinition]>>,
    ) -> Self {
        let identity = intern_kept_range_set(
            ranges.flat_owned_memory_ranges().clone(),
            HashedOrdMap::new(),
        );
        Self {
            ranges,
            residual: None,
            identity,
            premises,
            direct,
            caller_before_transfer: None,
            introduced_composites: ResourceContext::new(),
        }
    }

    fn with_residual(&self, residual: &ResourceContext) -> Self {
        let mut ranges = residual.flat_owned_memory_ranges().clone();
        for range in self.ranges.flat_owned_memory_ranges().keys() {
            crate::instrumentation::record_deterministic_work(1);
            if !ranges.contains_key(range) {
                ranges.insert(range.clone(), ());
            }
        }
        let composites = if self.direct.is_some() {
            residual.owned_composite_facts().clone()
        } else {
            HashedOrdMap::new()
        };
        let introduced_composites = if let Some(original) = &self.caller_before_transfer {
            let before = original.owned_composite_facts();
            let after = residual.owned_composite_facts();
            let mut introduced = ResourceContext::new();
            for change in before.diff(after) {
                crate::instrumentation::record_deterministic_work(1);
                let fact = match change {
                    HashedOrdMapChange::Added(fact) => fact,
                    HashedOrdMapChange::Changed(fact) if after.get(fact) > before.get(fact) => fact,
                    _ => continue,
                };
                introduced = introduced.unchecked_with_fact(fact.clone());
            }
            introduced
        } else {
            self.introduced_composites.clone()
        };
        let original_memory = self
            .caller_before_transfer
            .as_ref()
            .map(|original| original.memory_input_facts().clone())
            .unwrap_or_default();
        Self {
            ranges: self.ranges.clone(),
            residual: Some(residual.clone()),
            identity: intern_kept_range_set_with_exclusions(
                ranges,
                composites,
                original_memory,
                introduced_composites.owned_composite_facts().clone(),
                residual.memory_input_facts().clone(),
            ),
            premises: self.premises.clone(),
            direct: self.direct.clone(),
            caller_before_transfer: self.caller_before_transfer.clone(),
            introduced_composites,
        }
    }

    /// The ranges of `fact`, one of the residual's composites, when its
    /// family is argument-direct.
    fn direct_ranges(&self, fact: &ResourceFact) -> Vec<MemoryRange> {
        let (Some(direct), Resource::Composite { name, .. }) = (&self.direct, fact.resource())
        else {
            return Vec::new();
        };
        let Ok(index) = direct.binary_search_by(|definition| definition.name().cmp(name)) else {
            return Vec::new();
        };
        let definition = &direct[index];
        if !definition.has_argument_direct_body() {
            return Vec::new();
        }
        crate::kernel::functions::argument_direct_composite_ranges(
            fact,
            std::slice::from_ref(definition),
        )
    }

    /// Recorded caller ranges, for state diagnostics: the listed
    /// ranges and those of every argument-direct composite.
    pub(crate) fn diagnostic_ranges(&self) -> ResourceContext {
        let mut ranges = self.identity.ranges.clone();
        for fact in self.identity.composites.keys() {
            for range in self.direct_ranges(fact) {
                ranges.insert(range, ());
            }
        }
        ResourceContext::new()
            .unchecked_with_facts(ranges.keys().cloned().map(ResourceFact::own_memory))
            .unchecked_with_facts(
                self.identity
                    .memory_inputs
                    .keys()
                    .filter(|fact| fact.is_view())
                    .cloned(),
            )
    }

    /// Recorded placement premises, for state diagnostics.
    pub(crate) fn diagnostic_premises(&self) -> &[(OldConditionTerm, bool)] {
        &self.premises
    }

    fn is_empty(&self) -> bool {
        self.identity.ranges.is_empty()
            && self.identity.composites.is_empty()
            && self.identity.memory_inputs.is_empty()
    }

    /// `assumptions` with the premises assumed, charged one unit each.
    fn placement(&self, assumptions: &PureFactContext) -> Option<PureFactContext> {
        if self.premises.is_empty() {
            return None;
        }
        Some(
            self.premises
                .iter()
                .fold(assumptions.clone(), |facts, (condition, value)| {
                    facts.assume_proposition(Proposition::condition_is(condition.clone(), *value))
                }),
        )
    }

    /// The kept memory recorded on the call havoc edge that derived `after`,
    /// if that edge is one: what a call's effect summary may keep beside its
    /// declared write set.
    pub(in crate::kernel) fn recorded_on(after: &SymbolicMemory) -> Option<Self> {
        let derivation = crate::kernel::intern_memory_ref(after).derivation()?;
        let MemoryDerivation::CallHavoc {
            kept_by_caller: Some(kept),
            ..
        } = &*derivation
        else {
            return None;
        };
        Some(kept.clone())
    }

    /// Whether one kept range holds every byte of the access, placed under
    /// `assumptions` and the recorded premises
    /// ([`PureFactContext::kept_range_holding_access`]).
    pub(in crate::kernel) fn holds_access(
        &self,
        pointer: &Address,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        self.range_holding(assumptions, None, pointer, bytes)
            .is_some()
    }

    /// Whether `range` is kept: listed, or a range of an argument-direct
    /// composite whose arguments spell its base.
    pub(in crate::kernel) fn contains_range(&self, range: &MemoryRange) -> bool {
        if self.identity.ranges.contains_key(range)
            || self
                .identity
                .memory_inputs
                .contains_key(&ResourceFact::view_memory(range.clone()))
        {
            return true;
        }
        let Some(residual) = self.direct.as_ref().and(self.residual.as_ref()) else {
            return false;
        };
        crate::kernel::assumptions::additive_base_spellings(range.base())
            .iter()
            .filter_map(|base| residual.unique_owned_composite_with_pointer_argument(base))
            .any(|fact| self.direct_ranges(fact).contains(range))
    }

    /// The kept range holding the access. `placement` is the premises already
    /// assumed into `assumptions`, when the caller has built it once.
    ///
    /// After checking the listed ranges, try bounded indexed candidates for
    /// an argument-direct owner. An ambiguous bucket supplies no candidate.
    pub(in crate::kernel) fn range_holding(
        &self,
        assumptions: &PureFactContext,
        placement: Option<&PureFactContext>,
        pointer: &Address,
        bytes: u32,
    ) -> Option<MemoryRange> {
        #[cfg(test)]
        KEPT_CALL_RANGE_QUERIES.with(|queries| queries.set(queries.get() + 1));
        let query = |ranges: &ResourceContext, include_views| {
            let context = placement.unwrap_or(assumptions);
            let place = || {
                if placement.is_none() {
                    self.placement(assumptions)
                } else {
                    None
                }
            };
            if include_views {
                context.kept_read_range_holding_access(ranges, place, pointer, bytes)
            } else {
                context.kept_range_holding_access(ranges, place, pointer, bytes)
            }
            .cloned()
        };
        // Opened instance bodies contribute ownership only. Surviving views
        // are supplied by the checked caller residual, recorded separately.
        query(&self.ranges, false)
            .or_else(|| {
                self.residual
                    .as_ref()
                    .and_then(|ranges| query(ranges, true))
            })
            .or_else(|| {
                let residual = self.direct.as_ref().and(self.residual.as_ref())?;
                let bases = assumptions.kept_frame_address_keys(pointer);
                // A covering original flat owner excludes unchanged folded
                // owners by exclusivity. A transferred owner may have been
                // repackaged, so still consider newly introduced composites.
                let residual = if self
                    .caller_before_transfer
                    .as_ref()
                    .is_some_and(|original| {
                        bases.iter().any(|base| {
                            original
                                .unique_owned_memory_fact_with_base(base)
                                .is_some_and(|fact| {
                                    fact.has_proven_positive_quantity(assumptions)
                                        && fact.memory_own_range().is_some_and(|range| {
                                            assumptions
                                                .kept_range_holds_access(range, pointer, bytes)
                                        })
                                })
                        })
                    }) {
                    &self.introduced_composites
                } else {
                    residual
                };
                let mut seen = BTreeSet::new();
                let mut covers = |fact: &ResourceFact| {
                    if !seen.insert(fact.clone()) {
                        return None;
                    }
                    let ranges = self.direct_ranges(fact);
                    if ranges.is_empty() {
                        return None;
                    }
                    query(
                        &ResourceContext::new_with_equalities(assumptions)
                            .unchecked_with_facts(ranges.into_iter().map(ResourceFact::own_memory)),
                        false,
                    )
                };
                bases
                    .iter()
                    .filter_map(|base| residual.unique_owned_composite_with_pointer_argument(base))
                    .find_map(&mut covers)
                    .or_else(|| {
                        let mut blocks = BTreeSet::from([&pointer.base]);
                        blocks.extend(bases.iter().map(|base| &base.base));
                        blocks
                            .into_iter()
                            .filter_map(|block| {
                                residual.unique_owned_composite_with_argument_block(block)
                            })
                            .find_map(covers)
                    })
            })
    }

    fn identity(&self) -> String {
        let mut identity = format!("kept-range-set:{};", self.identity.id);
        let mut premises = self
            .premises
            .iter()
            .map(|(condition, value)| havoc_condition_identity(condition, *value))
            .collect::<Vec<_>>();
        premises.sort();
        let _ = write!(identity, "premises:{};", premises.len());
        for premise in premises {
            let _ = write!(identity, "{}:", premise.len());
            identity.push_str(&premise);
        }
        identity
    }
}

impl CallKeptOwnership {
    /// Retain the actual pre-transfer caller composition, sharing its indexes.
    /// This is an exclusion index, never another source of kept ownership.
    pub(in crate::kernel) fn with_caller_before_transfer(
        mut self,
        caller: &ResourceContext,
    ) -> Self {
        if self.opened.direct.is_some() && !caller.flat_owned_memory_ranges().is_empty() {
            self.opened.caller_before_transfer = Some(caller.clone());
        }
        self
    }

    #[cfg(test)]
    pub(in crate::kernel) fn opened_resources_for_test(&self) -> &ResourceContext {
        &self.opened.ranges
    }

    pub(in crate::kernel) fn new(
        residual: ResourceContext,
        opened: CallKeptRanges,
        assumptions: &PureFactContext,
    ) -> Self {
        let placement = opened.placement(assumptions);
        Self {
            residual,
            opened,
            placement,
        }
    }

    /// The kept ownership a call havoc recorded on the edge that derived
    /// `after`, for a checker that re-derives that havoc without the caller's
    /// resources: the recorded ranges and premises stand in for the opened
    /// bodies. The write-set marker spells both, so a content-equal state
    /// whose edge was recorded first carries the same ones.
    pub(in crate::kernel) fn recorded_on(
        after: &SymbolicMemory,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        let kept = CallKeptRanges::recorded_on(after)?;
        // Use the exact residual state recorded by the producer;
        // the opened-body ranges and premises remain in `kept`.
        let residual = kept.residual.clone().unwrap_or_default();
        Some(Self::new(residual, kept, assumptions))
    }

    /// The readable member that holds every byte of the access, from the opened
    /// bodies or the residual's own flat members: one base-index lookup in
    /// each, never a scan.
    fn member_holding(
        &self,
        pointer: &Address,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> Option<MemoryRange> {
        self.opened
            .range_holding(assumptions, self.placement.as_ref(), pointer, bytes)
            .or_else(|| {
                assumptions
                    .readable_member_holding_access(&self.residual, pointer, bytes)
                    .cloned()
            })
    }
}

/// How the call havoc rule treats one cell.
enum CallHavocCellRule {
    /// Kept by separation or the checked flat caller frame.
    Separate,
    /// Kept because a surviving caller owner or view holds it.
    KeptByCaller,
    Dropped,
}

/// Whether a call havoc keeps the cell at this address: the one rule, asked
/// by the producer that applies it and by the checker that re-derives what the
/// producer would have written.
///
/// This is the *eager* half of a call's write set, and it is deliberately not
/// the resource tracker's `CallHavoc` arm: that arm is re-derived per query
/// against the querying context and may look through composite definitions,
/// while this one runs once, over every cell that may alias the write set
/// ([`call_havoc_candidates`]), in the producing context. The
/// two are compared in `docs/internals/resource-tracker.md`.
///
/// Unreachable local cells may be kept without an owned-range lookup. A write
/// set naming that local block directly or through a checked affine alias
/// uses the ordinary byte-disjointness rule, followed by what the caller
/// keeps owning ([`CallKeptOwnership`]). An interior field alias can write
/// part of a cached cell even when its start differs from the cell's start.
fn call_havoc_keeps_cell(
    pointer: &Address,
    value: &ProgramValue,
    mutable_ranges: &[MemoryRange],
    assumptions: &PureFactContext,
    kept: Option<&CallKeptOwnership>,
    preserve_local_slots: bool,
) -> CallHavocCellRule {
    // A string literal's storage cannot be modified by any C function
    // (C11 6.4.5p7), so no call writes it, whoever holds it.
    if matches!(pointer.base, AddressBase::StringLiteral { .. }) {
        return CallHavocCellRule::Separate;
    }
    if preserve_local_slots
        && pointer.base.is_local_block()
        // An opaque pointer may reach a local even when no exact alias has
        // yet been stated. Absence of an alias is not separation evidence.
        && mutable_ranges.iter().all(|range| !matches!(range.base().base, AddressBase::Symbolic(_)))
        && !mutable_ranges.iter().any(|range| {
            range.base().base == pointer.base
                || assumptions
                    .equality_graph
                    .pointer_in_block(range.base(), &pointer.base)
                    .is_some()
        })
    {
        return if mutable_ranges.iter().all(|range| {
            range.base().base == pointer.base
                || !pointers_proven_equal_for_memory_resolution(range.base(), pointer, assumptions)
        }) {
            CallHavocCellRule::Separate
        } else {
            CallHavocCellRule::Dropped
        };
    }
    let bytes = crate::kernel::reasoning::cell_access_byte_width(value);
    // Whole parameter runs are filtered by the flat caller frame already.
    // A partial borrow leaves the run as a candidate; apply the same rule
    // to its individual slots before consulting older compositions.
    if kept.is_some_and(|kept| {
        assumptions
            .parameter_partition_cell_base(&kept.residual, pointer, bytes)
            .is_some()
    }) {
        return CallHavocCellRule::Separate;
    }
    if assumptions.ranges_directly_disjoint_from_access(mutable_ranges, pointer, bytes)
        || assumptions.ranges_proven_disjoint_from_pointer(mutable_ranges, pointer)
    {
        return CallHavocCellRule::Separate;
    }
    match kept.and_then(|kept| kept.member_holding(pointer, bytes, assumptions)) {
        Some(_) => CallHavocCellRule::KeptByCaller,
        None => CallHavocCellRule::Dropped,
    }
}

/// Retain all flat residual owners and the opened-body ranges and premises
/// on the edge, including uncached members. The persistent set's canonical
/// identity distinguishes paths without enumerating unrelated owners.
fn call_havoc_kept_ranges(kept: Option<&CallKeptOwnership>) -> Option<CallKeptRanges> {
    let kept = kept?;
    let recorded = kept.opened.with_residual(&kept.residual);
    (!recorded.is_empty()).then_some(recorded)
}

fn call_write_set_marker(
    variable: u64,
    mutable_ranges: &[MemoryRange],
    kept_ranges: Option<&CallKeptRanges>,
) -> AddressBase {
    let mut marker = format!(
        "call-write-set:{variable}:{}",
        memory_havoc_write_set_identity(mutable_ranges)
    );
    if let Some(kept_ranges) = kept_ranges {
        marker.push_str(":kept:");
        marker.push_str(&kept_ranges.identity());
    }
    marker.into()
}

/// Membership in the blocks a memory join keeps: a set, or a query a join
/// answers from the state's own indexes without listing every block.
pub(crate) trait BlockMembership {
    fn contains_block(&self, block: &AddressBase) -> bool;
}

impl BlockMembership for BTreeSet<AddressBase> {
    fn contains_block(&self, block: &AddressBase) -> bool {
        self.contains(block)
    }
}

impl BlockMembership for LocalEnvironment {
    fn contains_block(&self, block: &AddressBase) -> bool {
        self.names_with_slot_in(block)
            .into_iter()
            .any(|name| matches!(self.bindings.get(name), Some(LocalBinding::Object { .. })))
    }
}

/// Whether a havoc that preserves borrows keeps the cell at this address: the
/// one rule, asked by the loop head and by the interface join.
///
/// Unlike a call havoc this is not a separation question at all. A loop body,
/// or the arm of a branch the join is merging, may write through any pointer
/// it can reach, so the only cells that survive are the ones something else
/// guarantees: storage the function declared and did not expose
/// (`preserved_blocks`), and bytes an active borrow protects from being written
/// at all. Only indexed protection at the exact coordinate origin retains a value;
/// unknown relative bounds forget it without searching the ledger. That is why it consults
/// the ledger rather than the assumptions, and
/// why the resource tracker's havoc arms cannot answer it.
///
/// A cell whose width is unknown fails closed, because keeping its value on a
/// borrow the ledger would have permitted a write through is a promise nothing
/// proved (`docs/internals/stable-views.md`).
fn borrow_preserving_havoc_keeps_cell(
    pointer: &Address,
    byte_width: u32,
    preserved_blocks: &dyn BlockMembership,
    ledger: Option<&crate::kernel::borrows::BorrowLedger>,
) -> bool {
    preserved_blocks.contains_block(&pointer.base)
        || ledger.is_some_and(|ledger| {
            byte_width != 0
                && ledger.has_indexed_memory_overlap(&MemoryRange::new_with_element_width(
                    pointer.clone(),
                    OldMachineTerm::constant(0),
                    OldMachineTerm::constant(byte_width),
                    1,
                ))
        })
}

/// [`borrow_preserving_havoc_keeps_cell`] for every slot of a run at once. A run
/// in a preserved block keeps every slot; outside one, a slot survives only
/// where a borrow protects its bytes, so no borrow over any of the run's bytes
/// keeps none. Anything else is asked slot by slot. The run's slots hold no
/// typed union views (a run is never seeded beside them), so each slot's
/// width is its value's.
fn borrow_preserving_havoc_keeps_run(
    run: &CellRun,
    preserved_blocks: &dyn BlockMembership,
    ledger: Option<&crate::kernel::borrows::BorrowLedger>,
) -> (SlotSet, crate::kernel::primitives::RuleAnswer) {
    let exact = crate::kernel::primitives::RuleAnswer::Exact;
    if preserved_blocks.contains_block(&run.base().base) {
        return (SlotSet::All, exact);
    }
    let Some(ledger) = ledger else {
        return (SlotSet::Nothing, exact);
    };
    let whole = MemoryRange::new_with_element_width(
        run.base().clone(),
        OldMachineTerm::constant(0),
        OldMachineTerm::constant(
            (run.count().saturating_sub(1))
                .saturating_mul(run.element_width())
                .saturating_add(run.value_width()),
        ),
        1,
    );
    if !ledger.has_indexed_memory_overlap(&whole) {
        // An unindexable whole range can contain indexable individual slots.
        // Forgetting the whole run is sound but may discard extra knowledge;
        // forget_cached_values records those dropped slots.
        (
            SlotSet::Nothing,
            crate::kernel::primitives::RuleAnswer::Sound,
        )
    } else {
        (SlotSet::PerSlot, exact)
    }
}

/// The union of the arms' maps, built from the first arm's by the entries
/// another arm adds to it. An entry two arms hold with different values is
/// returned as the error. Only the entries on which an arm differs from the
/// first are visited.
fn union_of_arm_maps<'a, K, V>(
    first: &HashedOrdMap<K, V>,
    others: impl Iterator<Item = &'a HashedOrdMap<K, V>>,
) -> Result<HashedOrdMap<K, V>, K>
where
    K: Ord + Clone + std::hash::Hash + 'a,
    V: Clone + PartialEq + std::hash::Hash + 'a,
{
    let mut union = first.clone();
    for other in others {
        for change in first.diff(other) {
            match change {
                HashedOrdMapChange::Removed(_) => {}
                HashedOrdMapChange::Changed(key) => return Err(key.clone()),
                HashedOrdMapChange::Added(key) => {
                    let value = other.get(key).expect("an added key is held").clone();
                    if let Some(existing) = union.insert(key.clone(), value.clone())
                        && existing != value
                    {
                        return Err(key.clone());
                    }
                }
            }
        }
    }
    Ok(union)
}

/// The union of the arms' sets, visiting only what an arm holds that the
/// first does not, or the reverse.
fn union_of_arm_sets<'a, K>(
    first: &HashedOrdSet<K>,
    others: impl Iterator<Item = &'a HashedOrdSet<K>>,
) -> HashedOrdSet<K>
where
    K: Ord + Clone + std::hash::Hash + 'a,
{
    let mut union = first.clone();
    for other in others {
        for key in first.symmetric_difference(other) {
            union.insert(key.clone());
        }
    }
    union
}

/// The widest typed overlay recorded at each address, so that the borrow
/// question above covers every byte the cell can be read as.
fn union_overlay_widths(memory: &SymbolicMemory) -> BTreeMap<Address, u32> {
    let mut widths = BTreeMap::<Address, u32>::new();
    for (pointer, program_type) in memory.union_cells.keys() {
        widths
            .entry(pointer.clone())
            .and_modify(|width| *width = (*width).max(program_type.byte_width()))
            .or_insert_with(|| program_type.byte_width());
    }
    widths
}

/// Whether a heap allocation's recorded entry (its base) may contain
/// `pointer`.
///
/// The deciding rule is the equality invariant: differently spelled pointer
/// blocks are not separate unless [`AddressBase::proven_distinct`] or the
/// assumptions say so, so two edges control every answer. Entries whose block
/// is proven distinct from the query pointer's never contain it. Entries in a
/// block merely spelled differently do, once an assumed pointer equality names
/// one address under the two spellings; a tried interior-with-offset alias is
/// answered `false` here. That negative answer is not separation evidence:
/// the free-retirement path separately requires separation before keeping a
/// cached cell, and clears whole blocks for known aliases of the base.
fn heap_allocation_may_contain_pointer(
    base: &Address,
    pointer: &Address,
    assumptions: &PureFactContext,
) -> bool {
    #[cfg(test)]
    HEAP_CONTAINMENT_CHECKS.with(|checks| checks.set(checks.get() + 1));
    if base != pointer && base.base.proven_distinct(&pointer.base) {
        return false;
    }
    if base.base != pointer.base {
        return base.offset == pointer.offset
            && pointers_proven_equal_for_memory_resolution(base, pointer, assumptions);
    }
    if base.base != AddressBase::ExternalArgument {
        return true;
    }

    external_argument_offset_derives_from(base, pointer)
}

#[cfg(test)]
thread_local! {
    static HEAP_CONTAINMENT_CHECKS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Whether `pointer`, in the external argument block, is `base` or an address
/// built by adding to `base`'s offset.
fn external_argument_offset_derives_from(base: &Address, pointer: &Address) -> bool {
    if pointer.offset == base.offset {
        return true;
    }

    fn contains_base_offset(term: &AddressOffset, base: &AddressOffset) -> bool {
        match term.view() {
            OffsetView::Add(left, right) => {
                left == base
                    || right == base
                    || contains_base_offset(left, base)
                    || contains_base_offset(right, base)
            }
            OffsetView::Constant(_)
            | OffsetView::Variable(_)
            | OffsetView::Int32Scaled { .. }
            | OffsetView::Int64Scaled { .. } => false,
        }
    }

    contains_base_offset(&pointer.offset, &base.offset)
}

/// The one state a pure-function pointer argument is anchored to when the
/// callee provably reads no memory.
///
/// Such a function is a function of its argument values, so the ambient
/// state in the argument term is dead weight — and live weight would be
/// worse than dead: it makes the same proposition a different term on either
/// side of any C write, which is what stopped a `fold` from discharging a
/// body fact applying a pure predicate to a pointer. The state is empty, so
/// nothing can be read through it by construction, and it is cached per thread
/// so repeated uses share one storage root.
pub fn value_independent_click_memory() -> SymbolicMemory {
    thread_local! {
        static CANONICAL: SymbolicMemory = SymbolicMemory::new();
    }
    CANONICAL.with(Clone::clone)
}

impl SymbolicMemory {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_block(
        mut self,
        block: impl Into<AddressBase>,
        size: impl Into<crate::kernel::LayoutSize>,
    ) -> Self {
        let size: crate::kernel::LayoutSize = size.into();
        let block = block.into();
        // Havoc marker blocks mean "the state may have changed", never "a
        // fresh block appeared"; recording a benign block-declaration edge
        // for one would launder the havoc (conventions.md's soundness trap,
        // pinned by `conditions_equal_modulo_proven_states_needs_frame_
        // evidence`). The havoc producers insert their markers directly,
        // but tests and any future caller may write them through this
        // constructor, so the refusal lives here.
        if block.is_havoc_block() || block.is_call_havoc_block() {
            let diagnostic_base = self.clone();
            std::sync::Arc::make_mut(&mut self.blocks)
                .insert(block.clone(), MemoryBlock::new(size));
            self.record_diagnostic_transform(
                "insert havoc marker",
                vec![diagnostic_base],
                vec![ProgramValue::pointer(Address::new(
                    block,
                    AddressOffset::constant(0),
                ))],
            );
            return self;
        }
        let base = intern_derivation_base(&mut self);
        std::sync::Arc::make_mut(&mut self.blocks).insert(block.clone(), MemoryBlock::new(size));
        record_memory_derivation(&mut self, MemoryDerivation::BlockDeclared { base, block });
        self
    }

    /// Declared automatic scalars use allocation ownership, never the legacy
    /// implicit local access rule. One block lookup is independent of other cells.
    pub(in crate::kernel) fn requires_explicit_scalar_ownership(&self, pointer: &Address) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        self.blocks
            .get(&pointer.base)
            .is_some_and(|block| block.declared_scalar_type.is_some())
    }

    /// The declared class of the object `pointer` lies in, when its block
    /// records one (`design/effective-types.md`).
    pub(in crate::kernel) fn declared_class(
        &self,
        pointer: &Address,
    ) -> Option<crate::kernel::effective_type::CAccessClass> {
        crate::instrumentation::record_deterministic_work(1);
        self.blocks.get(&pointer.base)?.declared_class.clone()
    }

    pub(crate) fn has_boolean_cell_type(&self, pointer: &Address) -> bool {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        self.declared_class(pointer)
            .or_else(|| self.heap_effective_class(pointer))
            == Some(CAccessClass::Scalar(CScalarClass::Bool))
    }

    /// The effective type a C store gave the heap cell starting at
    /// `pointer`, while the cell still holds the value that store wrote
    /// (`design/effective-types.md`).
    pub(in crate::kernel) fn heap_effective_class(
        &self,
        pointer: &Address,
    ) -> Option<crate::kernel::effective_type::CAccessClass> {
        if !matches!(pointer.base, AddressBase::Heap(_)) {
            return None;
        }
        self.heap
            .effective_types
            .class_at(pointer, self.cells.explicitly_stored_value(pointer))
    }

    /// Records the effective type a C store of `value` through an lvalue of
    /// `class` gives the heap cell at `pointer`, without the store; a test
    /// setup of a record a store would have left.
    #[cfg(test)]
    pub(in crate::kernel) fn with_heap_effective_type(
        mut self,
        pointer: &Address,
        width: u32,
        class: Option<crate::kernel::effective_type::CAccessClass>,
        value: &ProgramValue,
    ) -> Self {
        if !matches!(pointer.base, AddressBase::Heap(_)) {
            return self;
        }
        let mut record = self.heap.effective_types.clone();
        if record.record(pointer, width, class, value) {
            std::sync::Arc::make_mut(&mut self.heap).effective_types = record;
        }
        self
    }

    /// A fresh block whose object, or every element of it, has
    /// `declared_class` (`design/effective-types.md`). The class is part of
    /// the declaration, so the block-declared derivation covers it.
    pub(crate) fn with_classed_block(
        self,
        block: AddressBase,
        declared_class: Option<crate::kernel::effective_type::CAccessClass>,
        size: impl Into<crate::kernel::LayoutSize>,
    ) -> Self {
        self.with_classed_block_or_read_only(block, declared_class, size, false)
    }

    pub(in crate::kernel) fn with_classed_block_or_read_only(
        self,
        block: AddressBase,
        declared_class: Option<crate::kernel::effective_type::CAccessClass>,
        size: impl Into<crate::kernel::LayoutSize>,
        read_only: bool,
    ) -> Self {
        let Some(declared_class) = declared_class else {
            return self.with_block_or_read_only(block, size, read_only);
        };
        let mut memory = self;
        let base = intern_derivation_base(&mut memory);
        let mut declaration = MemoryBlock::new(size);
        declaration.declared_class = Some(declared_class);
        declaration.read_only = read_only;
        std::sync::Arc::make_mut(&mut memory.blocks).insert(block.clone(), declaration);
        record_memory_derivation(&mut memory, MemoryDerivation::BlockDeclared { base, block });
        memory
    }

    /// [`Self::with_classed_scalar_block`] with the class its kernel type
    /// gives.
    #[cfg(test)]
    pub(in crate::kernel) fn with_declared_scalar_block(
        self,
        block: AddressBase,
        size: u32,
        program_type: ProgramType,
    ) -> Self {
        self.with_classed_scalar_block(block, size, program_type, None)
    }

    /// Declares one complete automatic scalar, retaining its type while its
    /// cells are unwritten, forgotten, or accessed through character pointers.
    /// The scalar's declared class is `declared_class`, or what its kernel
    /// type gives (`design/effective-types.md`).
    pub(in crate::kernel) fn with_classed_scalar_block(
        mut self,
        block: AddressBase,
        size: impl Into<crate::kernel::LayoutSize>,
        program_type: ProgramType,
        declared_class: Option<crate::kernel::effective_type::CAccessClass>,
    ) -> Self {
        let base = intern_derivation_base(&mut self);
        let mut declaration = MemoryBlock::new(size);
        declaration.declared_scalar_type = Some(program_type);
        declaration.declared_class = declared_class
            .or_else(|| crate::kernel::effective_type::CAccessClass::of_kernel_type(program_type));
        std::sync::Arc::make_mut(&mut self.blocks).insert(block.clone(), declaration);
        record_memory_derivation(&mut self, MemoryDerivation::BlockDeclared { base, block });
        self
    }

    /// Complete scalar construction without changing its size, type, cells,
    /// ownership, or allocation generation. Checked declaration execution is
    /// the only caller; later alias writes see the block's read-only status.
    pub(in crate::kernel) fn freeze_declared_scalar(self, block: &AddressBase) -> Self {
        assert!(
            self.blocks
                .get(block)
                .expect("declared scalar block")
                .declared_scalar_type
                .is_some()
        );
        self.freeze_declared_object(block, None)
    }

    /// An aggregate with temporary lifetime cannot be modified (C11 6.2.4p8).
    pub(in crate::kernel) fn freeze_aggregate_result(
        self,
        block: &AddressBase,
        declared_class: Option<crate::kernel::effective_type::CAccessClass>,
    ) -> Self {
        self.freeze_declared_object(block, declared_class)
    }

    pub(in crate::kernel) fn freeze_declared_object(
        mut self,
        block: &AddressBase,
        declared_class: Option<crate::kernel::effective_type::CAccessClass>,
    ) -> Self {
        let base = intern_derivation_base(&mut self);
        let mut declaration = self
            .blocks
            .get(block)
            .expect("declared object block")
            .clone();
        declaration.declared_class = declared_class.or(declaration.declared_class);
        declaration.read_only = true;
        std::sync::Arc::make_mut(&mut self.blocks).insert(block.clone(), declaration);
        record_memory_derivation(
            &mut self,
            MemoryDerivation::BlockDeclared {
                base,
                block: block.clone(),
            },
        );
        self
    }

    /// Describe initially unwritten complete-object storage. This builds a
    /// proof-entry state, not an allocation transition or lifetime reset:
    /// existing writes remain recorded, a symbolic identity can still alias
    /// arguments, and no memory-DAG transport edge is granted.
    pub fn with_uninitialized_block(mut self, block: impl Into<AddressBase>, size: u32) -> Self {
        let diagnostic_base = self.clone();
        let block = block.into();
        std::sync::Arc::make_mut(&mut self.blocks).insert(block.clone(), MemoryBlock::new(size));
        self.record_diagnostic_transform(
            "declare uninitialized block",
            vec![diagnostic_base],
            vec![
                ProgramValue::pointer(Address::new(block.clone(), AddressOffset::constant(0))),
                ProgramValue::Int32(size.into()),
            ],
        );
        self.with_uninitialized_object(Address::new(block, AddressOffset::constant(0)), size)
    }

    /// [`Self::with_uninitialized_block`] for a block of `size`, a number or
    /// a symbolic layout's `sizeof`, whose every byte is unwritten.
    pub fn with_uninitialized_block_of(
        mut self,
        block: impl Into<AddressBase>,
        size: crate::kernel::LayoutSize,
    ) -> Self {
        let crate::kernel::LayoutSize::Of(_) = size else {
            return self.with_uninitialized_block(block, size.concrete());
        };
        let block = block.into();
        std::sync::Arc::make_mut(&mut self.blocks).insert(
            block.clone(),
            MemoryBlock::with_symbolic_size(AllocationSize::new(
                size.term(),
                crate::kernel::AllocationSizeKind::UInt64,
            )),
        );
        self.with_uninitialized_object(
            Address::new(block, AddressOffset::constant(0)),
            Self::UNBOUNDED_UNWRITTEN_SPAN,
        )
    }

    /// The span of an unwritten footprint whose length is not a constant,
    /// such as `owns uninitialized(p[0..n])`: every byte from its start to the
    /// end of the block is treated as possibly unwritten. That is
    /// conservative for other memory of the same block, which then needs
    /// write or `defined` evidence too.
    pub(crate) const UNBOUNDED_UNWRITTEN_SPAN: u32 = u32::MAX;

    /// Record an unwritten object footprint without declaring or resizing its
    /// containing allocation. Proof-entry ownership supplies its storage
    /// authority and liveness separately; this marker supplies neither.
    pub fn with_uninitialized_object(mut self, pointer: Address, size: u32) -> Self {
        let diagnostic_base = self.clone();
        std::sync::Arc::make_mut(&mut self.heap)
            .uninitialized_objects
            .insert(pointer.clone(), size);
        self.record_diagnostic_transform(
            "mark uninitialized object",
            vec![diagnostic_base],
            vec![
                ProgramValue::pointer(pointer.clone()),
                ProgramValue::Int32(size.into()),
            ],
        );
        self
    }

    /// A conservative overlap query over only potentially aliasing tracked
    /// objects. Different symbolic spellings do not establish separation.
    pub(in crate::kernel) fn may_read_uninitialized_object(
        &self,
        pointer: &Address,
        bytes: u32,
    ) -> bool {
        if bytes == 0 {
            return false;
        }
        AliasCandidates::of_block(&pointer.base).any_entry(
            &self.heap.uninitialized_objects,
            |base, size| {
                crate::instrumentation::record_deterministic_work(1);
                if *size == 0 {
                    return false;
                }
                if base.base == pointer.base
                    && let (Some(start), Some(at)) =
                        (base.offset.as_const(), pointer.offset.as_const())
                    && let (Some(end), Some(read_end)) = (
                        start.checked_add(i64::from(*size)),
                        at.checked_add(i64::from(bytes)),
                    )
                {
                    return at < end && start < read_end;
                }
                // Array parameters share the external argument block. As for
                // a heap allocation there, a read belongs to the object only
                // when its address is built from the object's own base; any
                // other parameter's memory is held by a resource of its own,
                // which a valid context keeps disjoint from this one.
                if base.base == AddressBase::ExternalArgument
                    && pointer.base == AddressBase::ExternalArgument
                {
                    return external_argument_offset_derives_from(base, pointer);
                }
                true
            },
        )
    }

    pub(in crate::kernel) fn with_block_or_read_only(
        self,
        block: impl Into<AddressBase>,
        size: impl Into<crate::kernel::LayoutSize>,
        read_only: bool,
    ) -> Self {
        if read_only {
            self.with_read_only_block(block, size)
        } else {
            self.with_block(block, size)
        }
    }

    pub(in crate::kernel) fn with_read_only_block(
        mut self,
        block: impl Into<AddressBase>,
        size: impl Into<crate::kernel::LayoutSize>,
    ) -> Self {
        let block = block.into();
        let base = intern_derivation_base(&mut self);
        std::sync::Arc::make_mut(&mut self.blocks)
            .insert(block.clone(), MemoryBlock::read_only(size));
        record_memory_derivation(&mut self, MemoryDerivation::BlockDeclared { base, block });
        self
    }

    /// Adds a synthetic block without claiming that it was declared by a
    /// program transition. Symbolic aggregate return values use this to make
    /// their known layout available for bounds checks while keeping the
    /// symbolic load identity independent of the caller's memory state.
    pub(in crate::kernel) fn with_block_without_derivation(
        mut self,
        block: impl Into<AddressBase>,
        size: impl Into<crate::kernel::LayoutSize>,
    ) -> Self {
        let diagnostic_base = self.clone();
        let block = block.into();
        let size: crate::kernel::LayoutSize = size.into();
        std::sync::Arc::make_mut(&mut self.blocks).insert(block.clone(), MemoryBlock::new(size));
        self.record_diagnostic_transform(
            "declare synthetic block",
            vec![diagnostic_base],
            vec![
                ProgramValue::pointer(Address::new(block.clone(), AddressOffset::constant(0))),
                match size {
                    crate::kernel::LayoutSize::Bytes(bytes) => ProgramValue::Int32(bytes.into()),
                    crate::kernel::LayoutSize::Of(_) => ProgramValue::UInt64(size.term()),
                },
            ],
        );
        self
    }

    /// Ends the lifetime of one automatic-storage object at a function exit
    /// or before a declaration is re-entered. The tombstone is semantic: it
    /// makes aliases to the old object invalid instead of merely making an
    /// eventual load unresolved because the block disappeared.
    pub(crate) fn without_local_block(&self, block: &AddressBase) -> Self {
        if !self.blocks.contains_key(block) && self.forgotten.ended_local_blocks.contains(block) {
            return self.clone();
        }

        let mut memory = self.clone();
        let base = intern_derivation_base(&mut memory);
        std::sync::Arc::make_mut(&mut memory.blocks).remove(block);
        // Only the retired block's own cells go: one key range each, and a
        // run of the block (a zero-filled automatic array) as a whole.
        let own = AliasCandidates::only_block(block);
        memory.forget_cached_values(
            ForgetScope::candidates(&own),
            |_, _| CachedValueFate::Retired,
            |_| {
                (
                    SlotSet::Nothing,
                    crate::kernel::primitives::RuleAnswer::Exact,
                )
            },
        );
        let forgotten = std::sync::Arc::make_mut(&mut memory.forgotten);
        forgotten.ended_local_blocks.insert(block.clone());
        if !block_is_never_address_taken_local(block) {
            forgotten
                .ended_addressable_local_blocks
                .insert(block.clone());
        }
        // A later object is uninitialized until written; the tombstone
        // already refuses every access to this one.
        if own.any_entry(memory.heap.initialized.as_map(), |_, _| true)
            || own.any_entry(memory.heap.initialized.partial_map(), |_, _| true)
        {
            std::sync::Arc::make_mut(&mut memory.heap)
                .initialized
                .forget_block(block);
        }
        record_memory_derivation(
            &mut memory,
            MemoryDerivation::LocalLifetimeEnded {
                base,
                block: block.clone(),
            },
        );
        memory
    }

    pub(in crate::kernel) fn free_heap_block(
        self,
        pointer: &Address,
        assumptions: &PureFactContext,
    ) -> Result<Self, InvalidFree> {
        self.free_heap_block_with_owned_frame(pointer, assumptions, &ResourceContext::new())
    }

    /// Apply a free after execution consumed its full allocation ownership.
    /// `kept_owners` is the checked residual frame, never the input context:
    /// its owners coexist with the consumed bytes and survive their retirement.
    pub(in crate::kernel) fn free_heap_block_with_owned_frame(
        self,
        pointer: &Address,
        assumptions: &PureFactContext,
        kept_owners: &ResourceContext,
    ) -> Result<Self, InvalidFree> {
        self.free_heap_block_and_owned_pointer_frames(pointer, assumptions, kept_owners)
            .map(|(memory, _)| memory)
    }

    /// The retained pointer cells whose frames need the checked ownership
    /// context, collected by the free's own retention decision. The executor
    /// names their two reads and publishes their equalities beside the free.
    pub(in crate::kernel) fn free_heap_block_and_owned_pointer_frames(
        mut self,
        pointer: &Address,
        assumptions: &PureFactContext,
        kept_owners: &ResourceContext,
    ) -> Result<(Self, Vec<(Address, ProgramType)>), InvalidFree> {
        // An aliased spelling of this allocation (a contract-returned pointer
        // proven equal to it, e.g. `ensures result == p`) is one address too.
        // Retiring through one identity has to retire it through both, else a
        // load through the other could read a stale cached cell or a stale
        // zeroed/uninitialized status after the free. Blocks proven distinct
        // from this allocation's own block keep everything.
        let mut aliased_blocks = BTreeSet::<AddressBase>::new();
        for alias in assumptions.exact_pointer_aliases(pointer) {
            if alias.base != pointer.base && !alias.base.proven_distinct(&pointer.base) {
                aliased_blocks.insert(alias.base.clone());
            }
        }
        if self.heap.deallocated_allocations.contains_key(pointer) {
            return Err(InvalidFree::DoubleFree);
        }
        // Every heap entry and cell this free can retire is in a block not
        // proven distinct from the freed pointer's: `heap_allocation_may_
        // contain_pointer` answers `false` for every other block, and the
        // aliased spellings above are not proven distinct by construction.
        let candidates = AliasCandidates::of_block(&pointer.base);
        if !self.heap.live_allocations.contains_key(pointer) {
            return Err(
                if candidates.any_entry(&self.heap.live_allocations, |base, _| {
                    heap_allocation_may_contain_pointer(base, pointer, assumptions)
                }) {
                    InvalidFree::InteriorPointer
                } else {
                    InvalidFree::NonHeapPointer
                },
            );
        }
        // The edge's base is the memory the free starts from, interned before
        // any of its own edits: a base taken after removing the allocation
        // would be a state no constructor recorded.
        let base = Some(intern_derivation_base(&mut self));
        let bytes = std::sync::Arc::make_mut(&mut self.heap)
            .live_allocations
            .remove(pointer)
            .expect("the live allocation was found above");
        if pointer.base != AddressBase::ExternalArgument {
            std::sync::Arc::make_mut(&mut self.blocks).remove(&pointer.base);
        }
        for aliased in &aliased_blocks {
            std::sync::Arc::make_mut(&mut self.blocks).remove(aliased);
        }
        std::sync::Arc::make_mut(&mut self.heap)
            .deallocated_allocations
            .insert(pointer.clone(), bytes.clone());
        // Statuses recorded under an aliased spelling of this same allocation
        // die with it: keeping them would let loads through that spelling see
        // uninitialized or zeroed-after-free knowledge nobody retired.
        let mut retired = aliased_blocks.clone();
        retired.insert(pointer.base.clone());
        let retired_key = |base: &Address| {
            retired.contains(&base.base) && base.offset == pointer.offset
                || heap_allocation_may_contain_pointer(base, pointer, assumptions)
        };
        let heap = std::sync::Arc::make_mut(&mut self.heap);
        let freed_within = |base: &Address| retired_key(base);
        candidates.retain_map(&mut heap.live_allocations, |base, _| !freed_within(base));
        candidates.retain_set(&mut heap.uninitialized_allocations, |base| {
            !freed_within(base)
        });
        candidates.retain_set(&mut heap.zeroed_allocations, |base| !freed_within(base));
        candidates.retain_map(&mut heap.zeroed_prefix_allocations, |base, _| {
            !freed_within(base)
        });
        heap.initialized
            .retain_candidates(&candidates, |cell, _| !freed_within(cell));
        // Absence from the retirement set is not separation: a different
        // block spelling may be an interior alias of this allocation.
        // The executor has consumed the allocation's complete ownership and
        // checked the surviving frame. Its remaining owners are separate
        // from those consumed bytes by construction. Select the owner of
        // this complete cell through the access index; do not rediscover the
        // freed block's ownership (which may have symbolic size).
        let mut pointer_frames = Vec::new();
        self.forget_cached_values(
            ForgetScope::candidates(&candidates),
            |cell, value| {
                if aliased_blocks.contains(&cell.base) || freed_within(cell) {
                    CachedValueFate::Retired
                } else if pointer.blocks_proven_distinct(cell) {
                    CachedValueFate::Kept
                } else if kept_owners
                    .owned_memory_member_covering_extent(
                        cell,
                        match value {
                            CachedValue::Cell(value) => {
                                crate::kernel::assumptions::access_extent_of_value(value)
                            }
                            CachedValue::UnionView(..) => {
                                crate::kernel::AccessExtent::Bytes(value.byte_width())
                            }
                        },
                        assumptions,
                    )
                    .is_some()
                {
                    let value_type = match value {
                        CachedValue::Cell(value) => value.program_type(),
                        CachedValue::UnionView(value_type, _) => value_type,
                    };
                    // Function pointers do not yet use logical version reads.
                    if value_type.pointee_type().is_some()
                        && !matches!(value_type, ProgramType::FunctionPointer(_))
                        && !crate::instrumentation::in_uncharged_debug_check()
                    {
                        pointer_frames.push((cell.clone(), value_type));
                    }
                    CachedValueFate::Kept
                } else {
                    CachedValueFate::Forgotten
                }
            },
            ask_every_slot,
        );
        if let Some(base) = base {
            record_memory_derivation(
                &mut self,
                MemoryDerivation::HeapFreed {
                    base,
                    allocation_base: pointer.clone(),
                    bytes: bytes.bytes().clone(),
                },
            );
        }
        Ok((self, pointer_frames))
    }

    pub(in crate::kernel) fn live_heap_block_size(
        &self,
        pointer: &Address,
    ) -> Option<&AllocationSize> {
        self.heap.live_allocations.get(pointer)
    }

    pub(crate) fn is_live_heap_address(
        &self,
        pointer: &Address,
        assumptions: &PureFactContext,
    ) -> bool {
        // An allocation based in a block proven distinct from the pointer's
        // never contains it, so only the candidate entries are asked.
        self.heap.live_allocations.contains_key(pointer)
            || AliasCandidates::of_block(&pointer.base)
                .any_entry(&self.heap.live_allocations, |base, _| {
                    heap_allocation_may_contain_pointer(base, pointer, assumptions)
                })
    }

    pub(in crate::kernel) fn heap_live_allocation_bases(&self) -> impl Iterator<Item = &Address> {
        self.heap.live_allocations.keys()
    }

    pub(in crate::kernel) fn is_uninitialized_heap_address(
        &self,
        pointer: &Address,
        byte_width: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        let candidates = AliasCandidates::of_block(&pointer.base);
        candidates.any_element(&self.heap.uninitialized_allocations, |base| {
            heap_allocation_may_contain_pointer(base, pointer, assumptions)
        }) || candidates.any_entry(&self.heap.zeroed_prefix_allocations, |base, prefix| {
            let Some(offset) = pointer.offset.as_const() else {
                return false;
            };
            let Ok(offset) = u32::try_from(offset) else {
                return false;
            };
            let Some(end) = offset.checked_add(byte_width) else {
                return false;
            };
            heap_allocation_may_contain_pointer(base, pointer, assumptions)
                && prefix.as_const().is_some_and(|prefix| end > prefix)
        })
    }

    /// Drops the zeroed reading of any allocation a write set can reach.
    ///
    /// "Reads as zero where unwritten" is a claim about an allocation's
    /// contents, so a write the caller cannot see invalidates it exactly as
    /// it invalidates a stored cell. The blanket status is dropped for the
    /// whole allocation rather than narrowed to a prefix: the write set bounds
    /// where a callee or loop body may store, not where it did.
    fn forget_zeroed_allocations_written_by(
        &mut self,
        mutable_ranges: &[MemoryRange],
        assumptions: &PureFactContext,
    ) {
        if mutable_ranges.is_empty() {
            return;
        }
        let written = |base: &Address| {
            mutable_ranges
                .iter()
                .any(|range| heap_allocation_may_contain_pointer(base, range.base(), assumptions))
        };
        // An allocation based in a block proven distinct from every range
        // base contains none of them.
        let candidates =
            AliasCandidates::of_blocks(mutable_ranges.iter().map(|range| &range.base().base));
        if !candidates.any_element(&self.heap.zeroed_allocations, |base| written(base))
            && !candidates.any_entry(&self.heap.zeroed_prefix_allocations, |base, _| {
                written(base)
            })
        {
            return;
        }
        let heap = std::sync::Arc::make_mut(&mut self.heap);
        candidates.retain_set(&mut heap.zeroed_allocations, |base| !written(base));
        candidates.retain_map(&mut heap.zeroed_prefix_allocations, |base, _| {
            !written(base)
        });
    }

    /// Whether a recorded cell or run slot holds a byte of
    /// `[pointer, pointer + byte_width)`.
    ///
    /// The exact-address lookups a load makes first miss a narrower cell
    /// stored strictly inside the loaded bytes and a wider cell containing
    /// them alike, so a zeroed allocation must not answer such a load as
    /// zero: the bytes a store wrote are no longer zero. For an offset with a
    /// constant line this is a bounded range query over the cells of that
    /// line from `WIDEST_CELL_BYTES - 1` below the load to its end, which is
    /// where any overlapping cell starts, plus the block's runs by byte range.
    /// An offset with no constant line is separated from a cell by no bound
    /// this question can read, so it answers `true` whenever its block holds
    /// a cell at all; the equal-cell scan before this question has already
    /// split off the cells it can relate to the load.
    pub(in crate::kernel) fn stored_bytes_overlap(
        &self,
        pointer: &Address,
        byte_width: u32,
    ) -> bool {
        /// The widest cell a store records, in bytes (`Int128`).
        const WIDEST_CELL_BYTES: i64 = 16;
        let (stem, start) = cell_store::offset_stem_and_constant(&pointer.offset);
        let end = start.saturating_add(i64::from(byte_width));
        let overlaps = |cell_offset: i64, cell_width: u32| {
            cell_offset < end && cell_offset.saturating_add(i64::from(cell_width)) > start
        };
        let mut visited = 0usize;
        let found = match stem {
            None => {
                let at = |offset: i64| pointer.with_offset(AddressOffset::constant(offset));
                let low = start.saturating_sub(WIDEST_CELL_BYTES - 1);
                let cell_overlaps =
                    self.cells
                        .concrete()
                        .range(at(low)..at(end))
                        .any(|(cell, value)| {
                            visited += 1;
                            cell.offset.as_const().is_some_and(|cell_offset| {
                                overlaps(
                                cell_offset,
                                crate::kernel::reasoning::memory_resolution::cell_access_byte_width(
                                    value.native(),
                                ),
                            )
                            })
                        });
                cell_overlaps
                    || self.cells.runs_in_block(&pointer.base).any(|run| {
                        visited += 1;
                        match run.base().offset.as_const() {
                            Some(run_start) => {
                                let bytes = u32::try_from(
                                    u64::from(run.count()) * u64::from(run.element_width()),
                                )
                                .unwrap_or(u32::MAX);
                                overlaps(run_start, bytes)
                            }
                            // A run based at a symbolic offset is not
                            // separated from the load by any constant.
                            None => true,
                        }
                    })
            }
            Some(_) => {
                let candidates = AliasCandidates::of_block(&pointer.base);
                visited += 1;
                candidates.entries(self.cells.concrete()).next().is_some()
                    || self.cells.candidate_runs(&candidates).next().is_some()
            }
        };
        crate::instrumentation::record_deterministic_work(visited);
        found
    }

    pub(in crate::kernel) fn is_zeroed_heap_address(
        &self,
        pointer: &Address,
        byte_width: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        // A zeroed allocation reads as zero only where nothing was stored
        // over the bytes the load reads; a store at another address can
        // still cover some of them.
        if self.stored_bytes_overlap(pointer, byte_width) {
            return false;
        }
        let candidates = AliasCandidates::of_block(&pointer.base);
        candidates.any_element(&self.heap.zeroed_allocations, |base| {
            heap_allocation_may_contain_pointer(base, pointer, assumptions)
        }) || candidates.any_entry(&self.heap.zeroed_prefix_allocations, |base, prefix| {
            let Some(offset) = pointer.offset.as_const() else {
                return false;
            };
            let Ok(offset) = u32::try_from(offset) else {
                return false;
            };
            let Some(end) = offset.checked_add(byte_width) else {
                return false;
            };
            heap_allocation_may_contain_pointer(base, pointer, assumptions)
                && prefix.as_const().is_some_and(|prefix| end <= prefix)
        })
    }

    pub(in crate::kernel) fn is_deallocated_heap_address(
        &self,
        pointer: &Address,
        assumptions: &PureFactContext,
    ) -> bool {
        AliasCandidates::of_block(&pointer.base)
            .any_entry(&self.heap.deallocated_allocations, |base, _| {
                heap_allocation_may_contain_pointer(base, pointer, assumptions)
            })
    }

    /// Whether no allocation has been freed in this state.
    pub(in crate::kernel) fn heap_has_no_deallocations(&self) -> bool {
        self.heap.deallocated_allocations.is_empty()
    }

    pub(in crate::kernel) fn shares_heap_deallocations_with(&self, other: &Self) -> bool {
        self.heap
            .deallocated_allocations
            .ptr_eq(&other.heap.deallocated_allocations)
    }

    #[cfg(test)]
    pub(in crate::kernel) fn take_heap_containment_checks() -> usize {
        HEAP_CONTAINMENT_CHECKS.with(|checks| checks.replace(0))
    }

    /// The deallocated allocation base that `pointer` provably points into,
    /// asked of the entries in `pointer`'s own block only.
    ///
    /// This is the evidence the pointer-value rules use: a pointer whose
    /// pointee's lifetime has ended has an indeterminate value (C11 6.2.4p2),
    /// and operating on it is undefined. Unlike a load, which also consults
    /// symbolic aliases, this looks up one block's key range, so an ordinary
    /// comparison or cast costs O(log n) plus that block's freed entries. A
    /// symbolic block that is not itself recorded as freed answers `None`.
    pub(in crate::kernel) fn deallocated_heap_allocation_holding(
        &self,
        pointer: &Address,
        assumptions: &PureFactContext,
    ) -> Option<Address> {
        if self.heap.deallocated_allocations.is_empty() {
            return None;
        }
        let candidates = AliasCandidates::only_block(&pointer.base);
        let mut visited = 0usize;
        let found = candidates
            .entries(&self.heap.deallocated_allocations)
            .find(|(base, _)| {
                visited += 1;
                heap_allocation_may_contain_pointer(base, pointer, assumptions)
            })
            .map(|(base, _)| base.clone());
        crate::instrumentation::record_deterministic_work(visited);
        found
    }

    /// Registers the exact base named by an allocation contract. Unlike a
    /// fresh `malloc`, this does not create a concrete block or imply that its
    /// existing bytes are uninitialized; access remains governed by the
    /// accompanying memory resources.
    pub(in crate::kernel) fn with_heap_allocation_claim(
        mut self,
        base: Address,
        bytes: AllocationSize,
    ) -> Option<Self> {
        if bytes.bytes().as_const() == Some(0)
            || self.heap.deallocated_allocations.contains_key(&base)
        {
            return None;
        }
        match self.heap.live_allocations.get(&base) {
            Some(existing) if existing != &bytes => None,
            Some(_) => Some(self),
            None => {
                let prior = Some(intern_derivation_base(&mut self));
                std::sync::Arc::make_mut(&mut self.heap)
                    .live_allocations
                    .insert(base, bytes);
                if let Some(prior) = prior {
                    record_memory_derivation(
                        &mut self,
                        MemoryDerivation::ContractAllocationClaimsChanged { base: prior },
                    );
                }
                Some(self)
            }
        }
    }

    /// Retires an input allocation at an opaque contract boundary.
    ///
    /// The contract leaves continuity undecided, so the callee may have freed
    /// the object. Forget content and allocation status under every spelling
    /// the path proves equal to the input base, without asserting a definite
    /// deallocation. Return resources install any post-call claim afterwards.
    pub(in crate::kernel) fn retire_contract_heap_allocation_claim(
        mut self,
        base: &Address,
        bytes: &OldMachineTerm,
        assumptions: &PureFactContext,
    ) -> Self {
        let prior = intern_derivation_base(&mut self);
        let mut retired_blocks = BTreeSet::from([base.base.clone()]);
        for alias in assumptions.exact_pointer_aliases(base) {
            if !alias.base.proven_distinct(&base.base) {
                retired_blocks.insert(alias.base.clone());
            }
        }
        let retired_claim = |candidate: &Address| {
            heap_allocation_may_contain_pointer(candidate, base, assumptions)
                || pointers_proven_equal_for_memory_resolution(candidate, base, assumptions)
        };
        // A symbolic alias block can hold cells at interior offsets. As at a
        // definite free, dropping that block's cached cells is conservative:
        // an undecided contract can replace the allocation entirely.
        let retired_cell = |candidate: &Address| {
            retired_blocks.contains(&candidate.base) || retired_claim(candidate)
        };

        // Neither predicate holds in a block proven distinct from the base's,
        // and the retired alias blocks are not proven distinct from it.
        let candidates = AliasCandidates::of_block(&base.base);
        let heap = std::sync::Arc::make_mut(&mut self.heap);
        candidates.retain_map(&mut heap.live_allocations, |candidate, _| {
            !retired_claim(candidate)
        });
        candidates.retain_set(&mut heap.uninitialized_allocations, |candidate| {
            !retired_claim(candidate)
        });
        candidates.retain_set(&mut heap.zeroed_allocations, |candidate| {
            !retired_claim(candidate)
        });
        candidates.retain_map(&mut heap.zeroed_prefix_allocations, |candidate, _| {
            !retired_claim(candidate)
        });
        heap.initialized
            .retain_candidates(&candidates, |candidate, _| !retired_cell(candidate));
        self.forget_cached_values(
            ForgetScope::candidates(&candidates),
            |candidate, _| {
                if retired_cell(candidate) {
                    CachedValueFate::Retired
                } else {
                    CachedValueFate::Kept
                }
            },
            ask_every_slot,
        );
        for block in &retired_blocks {
            if *block != AddressBase::ExternalArgument {
                std::sync::Arc::make_mut(&mut self.blocks).remove(block);
            }
        }
        // Losing an allocation's cached knowledge can otherwise re-intern as
        // an older empty state and drop this safety-critical edge. A
        // retirement inside its own call's havoc keeps that havoc's mark
        // instead: see `retirement_keeps_its_call_havocs_forget_mark`.
        use crate::kernel::resource_tracker::cell_source::retirement_keeps_its_call_havocs_forget_mark;
        if !retirement_keeps_its_call_havocs_forget_mark(&prior, base, bytes) {
            self.mark_forgotten_from(&prior);
        }
        record_memory_derivation(
            &mut self,
            MemoryDerivation::ContractAllocationRetired {
                base: prior,
                allocation_base: base.clone(),
                bytes: bytes.clone(),
            },
        );
        self
    }

    pub(in crate::kernel) fn with_pending_heap_allocation(
        self,
        base: Address,
        bytes: AllocationSize,
        zeroed: bool,
    ) -> Self {
        self.with_pending_typed_heap_allocation(base, bytes, zeroed, None)
    }

    pub(in crate::kernel) fn with_pending_typed_heap_allocation(
        mut self,
        base: Address,
        bytes: AllocationSize,
        zeroed: bool,
        object_class: Option<crate::kernel::effective_type::CAccessClass>,
    ) -> Self {
        let prior = Some(intern_derivation_base(&mut self));
        if let Some(class) = object_class {
            std::sync::Arc::make_mut(&mut self.heap)
                .pending_object_classes
                .insert(base.clone(), class);
        }
        std::sync::Arc::make_mut(&mut self.heap)
            .pending_allocations
            .insert(base.clone(), bytes.clone());
        if zeroed {
            std::sync::Arc::make_mut(&mut self.heap)
                .zeroed_pending_allocations
                .insert(base.clone());
        }
        if let Some(prior) = prior {
            record_memory_derivation(
                &mut self,
                MemoryDerivation::HeapAllocationPending {
                    base: prior,
                    allocation_base: base,
                    bytes: bytes.bytes().clone(),
                },
            );
        }
        self
    }

    pub(in crate::kernel) fn with_pending_heap_reallocation(
        mut self,
        base: Address,
        pending: PendingReallocation,
    ) -> Self {
        let diagnostic_base = self.clone();
        let arguments = vec![
            ProgramValue::pointer(base.clone()),
            ProgramValue::pointer(pending.old_pointer.clone()),
            pending.old_bytes.token_value(),
        ];
        std::sync::Arc::make_mut(&mut self.heap)
            .pending_reallocations
            .insert(base, pending);
        self.record_diagnostic_transform(
            "register pending reallocation",
            vec![diagnostic_base],
            arguments,
        );
        self
    }

    /// The runs of constant byte offsets of `block` the initialization
    /// record holds, ascending, as start and length. Costs the entries of
    /// the one block.
    pub(in crate::kernel) fn initialized_runs_in_block(
        &self,
        block: &AddressBase,
    ) -> Vec<(i64, u32)> {
        self.heap.initialized.constant_runs_in_block(block)
    }

    /// Whether execution still owns the unresolved success/failure choice of
    /// a fresh heap allocation. Proof-frontier branch selection uses this
    /// read-only query to avoid duplicating that independent path split.
    pub(crate) fn has_pending_heap_allocation(&self) -> bool {
        !self.heap.pending_allocations.is_empty()
    }

    /// Name the success identity already reserved by this allocation producer.
    /// This is a value observation, not evidence that allocation succeeded or
    /// that the object is still live. No facts or memory history are consulted.
    pub(crate) fn fresh_allocation_identity(&self, result: &Pointer) -> Option<Pointer> {
        let base = result.address();
        match base.base {
            AddressBase::Heap(_) => Some(result.clone()),
            AddressBase::Symbolic(variable) if self.heap.pending_allocations.contains_key(base) => {
                let resolved =
                    Address::new(AddressBase::Heap(variable.0), AddressOffset::constant(0));
                Some(crate::kernel::eval::rebase_resolved_allocation(
                    result, base, &resolved,
                ))
            }
            _ => None,
        }
    }

    pub(in crate::kernel) fn heap_identity_in_use(&self, identity: u64) -> bool {
        self.blocks.contains_key(&AddressBase::Heap(identity))
            || self
                .heap
                .deallocated_allocations
                .keys()
                .any(|base| base.base == AddressBase::Heap(identity))
            || self
                .heap
                .pending_allocations
                .keys()
                .any(|base| base.base == AddressBase::Symbolic(Variable(identity)))
    }

    /// Whether heap identity `identity` had been handed out by this
    /// state: live, freed, or pending. Identities are never reused within
    /// a proof, so an identity this answers false for is allocated after it.
    /// Allocation bases sit at offset zero, so each record is one lookup.
    pub(in crate::kernel) fn heap_identity_allocated(&self, identity: u64) -> bool {
        let base = |block| Address::new(block, AddressOffset::constant(0));
        self.blocks.contains_key(&AddressBase::Heap(identity))
            // An `allocates(result, n)` call's block, claimed by its contract.
            || self
                .heap
                .live_allocations
                .contains_key(&base(AddressBase::Heap(identity)))
            || self
                .heap
                .deallocated_allocations
                .contains_key(&base(AddressBase::Heap(identity)))
            || self
                .heap
                .pending_allocations
                .contains_key(&base(AddressBase::Symbolic(Variable(identity))))
    }

    /// Every heap identity [`Self::heap_identity_allocated`] answers true
    /// for, ascending. Costs the heap records this state holds.
    pub(in crate::kernel) fn allocated_heap_identities(&self) -> Vec<u64> {
        let heap_base = |identity| {
            Address::new(
                AddressBase::Heap(identity),
                AddressOffset::constant(i64::MIN),
            )
        };
        let mut identities = self
            .blocks
            .range(AddressBase::Heap(0)..AddressBase::Temporary(0))
            .filter_map(|(block, _)| match block {
                AddressBase::Heap(identity) => Some(*identity),
                _ => None,
            })
            .chain(
                self.heap
                    .live_allocations
                    .range(heap_base(0)..)
                    .map_while(|(base, _)| match base.base {
                        AddressBase::Heap(identity) => Some(identity),
                        _ => None,
                    }),
            )
            .chain(
                self.heap
                    .deallocated_allocations
                    .range(heap_base(0)..)
                    .map_while(|(base, _)| match base.base {
                        AddressBase::Heap(identity) => Some(identity),
                        _ => None,
                    }),
            )
            .chain(
                self.heap
                    .pending_allocations
                    .keys()
                    .filter_map(|base| match base.base {
                        AddressBase::Symbolic(variable) => Some(variable.0),
                        _ => None,
                    }),
            )
            .collect::<Vec<_>>();
        identities.sort_unstable();
        identities.dedup();
        identities
    }

    pub(in crate::kernel) fn resolve_pending_heap_allocation(
        mut self,
        base: &Address,
        succeeds: bool,
    ) -> Option<(Self, AllocationSize, Address)> {
        let prior = Some(intern_derivation_base(&mut self));
        let bytes = std::sync::Arc::make_mut(&mut self.heap)
            .pending_allocations
            .remove(base)?;
        let zeroed = std::sync::Arc::make_mut(&mut self.heap)
            .zeroed_pending_allocations
            .remove(base);
        let resolved_base = if succeeds {
            let AddressBase::Symbolic(variable) = base.base else {
                return None;
            };
            Address::new(AddressBase::Heap(variable.0), AddressOffset::constant(0))
        } else {
            Address::null()
        };
        let object_class = std::sync::Arc::make_mut(&mut self.heap)
            .pending_object_classes
            .remove(base);
        if succeeds {
            let mut block = MemoryBlock::with_symbolic_size(bytes.clone());
            block.declared_class = object_class;
            std::sync::Arc::make_mut(&mut self.blocks).insert(resolved_base.base.clone(), block);
            std::sync::Arc::make_mut(&mut self.heap)
                .live_allocations
                .insert(resolved_base.clone(), bytes.clone());
            if zeroed {
                std::sync::Arc::make_mut(&mut self.heap)
                    .zeroed_allocations
                    .insert(resolved_base.clone());
            } else {
                std::sync::Arc::make_mut(&mut self.heap)
                    .uninitialized_allocations
                    .insert(resolved_base.clone());
            }
            if let Some(prior) = prior {
                record_memory_derivation(
                    &mut self,
                    MemoryDerivation::HeapAllocated {
                        base: prior,
                        block: resolved_base.base.clone(),
                        bytes: bytes.bytes().clone(),
                    },
                );
            }
        } else if let Some(prior) = prior {
            record_memory_derivation(
                &mut self,
                MemoryDerivation::HeapAllocationFailed { base: prior },
            );
        }
        Some((self, bytes, resolved_base))
    }

    pub(in crate::kernel) fn resolve_pending_heap_reallocation(
        mut self,
        base: &Address,
        succeeds: bool,
        assumptions: &PureFactContext,
    ) -> Option<(Self, AllocationSize, Address, PendingReallocation)> {
        let diagnostic_base = self.clone();
        let pending = std::sync::Arc::make_mut(&mut self.heap)
            .pending_reallocations
            .remove(base)?;
        self.record_diagnostic_transform(
            "consume pending reallocation",
            vec![diagnostic_base.clone()],
            vec![ProgramValue::pointer(base.clone())],
        );
        let (mut memory, bytes, resolved_base) = if succeeds {
            self = self
                .free_heap_block(&pending.old_pointer, assumptions)
                .ok()?;
            self.resolve_pending_heap_allocation(base, true)?
        } else {
            self.resolve_pending_heap_allocation(base, false)?
        };
        if succeeds {
            if let Some(zeroed_prefix) = &pending.zeroed_prefix {
                std::sync::Arc::make_mut(&mut memory.heap)
                    .uninitialized_allocations
                    .remove(&resolved_base);
                if zeroed_prefix
                    .as_const()
                    .zip(bytes.bytes().as_const())
                    .is_some_and(|(prefix, bytes)| prefix == bytes)
                {
                    std::sync::Arc::make_mut(&mut memory.heap)
                        .zeroed_allocations
                        .insert(resolved_base.clone());
                } else {
                    std::sync::Arc::make_mut(&mut memory.heap)
                        .zeroed_prefix_allocations
                        .insert(resolved_base.clone(), zeroed_prefix.clone());
                }
            }
            memory.record_diagnostic_transform(
                "restore reallocation zeroed prefix",
                vec![diagnostic_base.clone()],
                vec![ProgramValue::pointer(resolved_base.clone())],
            );
            for (offset, value) in &pending.copied_cells {
                memory = memory.store(resolved_base.with_offset(offset.clone()), value.clone());
            }
            // Bytes the old block had initialized keep that, in the new
            // block, where no cached cell carried their value across.
            for (start, length) in &pending.initialized_prefix {
                memory = memory.with_initialized_object(
                    &resolved_base.with_offset(AddressOffset::constant(*start)),
                    *length,
                );
            }
        }
        Some((memory, bytes, resolved_base, pending))
    }

    pub(in crate::kernel) fn with_loop_memory_havoc_preserving_borrows(
        self,
        variable: Variable,
        preserved_blocks: &dyn BlockMembership,
        mutable_ranges: Option<&[MemoryRange]>,
        ledger: Option<&crate::kernel::borrows::BorrowLedger>,
    ) -> Self {
        self.loop_memory_havoc(
            variable,
            preserved_blocks,
            mutable_ranges,
            ledger,
            None,
            ForgetScope::Everywhere,
        )
    }

    pub(in crate::kernel) fn with_loop_memory_havoc_preserving_locals(
        self,
        variable: Variable,
        locals: &LocalEnvironment,
        mutable_ranges: Option<&[MemoryRange]>,
        ledger: Option<&crate::kernel::borrows::BorrowLedger>,
        kept_by_function: Option<CallKeptRanges>,
    ) -> Self {
        // The loop head has already abstracted every directly assigned
        // scalar. A cached scalar whose address the C source never takes
        // cannot be changed by the remaining, indirect writes.
        let candidates = AliasCandidates::every_block();
        let selected = self.cells.pointer_reachable_cells();
        self.loop_memory_havoc(
            variable,
            locals,
            mutable_ranges,
            ledger,
            kept_by_function,
            ForgetScope::Ordered {
                candidates: &candidates,
                selected: &selected,
                runs: None,
                cells_kept: &[],
            },
        )
    }

    #[cfg(test)]
    pub(in crate::kernel) fn with_loop_memory_havoc_preserving_frame(
        self,
        variable: Variable,
        preserved_blocks: &dyn BlockMembership,
        mutable_ranges: Option<&[MemoryRange]>,
        ledger: Option<&crate::kernel::borrows::BorrowLedger>,
        kept_by_function: Option<CallKeptRanges>,
    ) -> Self {
        self.loop_memory_havoc(
            variable,
            preserved_blocks,
            mutable_ranges,
            ledger,
            kept_by_function,
            ForgetScope::Everywhere,
        )
    }

    fn loop_memory_havoc(
        mut self,
        variable: Variable,
        preserved_blocks: &dyn BlockMembership,
        mutable_ranges: Option<&[MemoryRange]>,
        ledger: Option<&crate::kernel::borrows::BorrowLedger>,
        kept_by_function: Option<CallKeptRanges>,
        scope: ForgetScope<'_>,
    ) -> Self {
        // A loop body that may write memory can clobber, through some
        // pointer, any value it can reach. Drop cached values (cells and
        // typed union views alike) outside the preserved (scalar stack local)
        // blocks so loop-head and post-loop reads do not observe stale
        // pre-loop values. A checked footprint is retained on the derivation
        // edge for disjoint-load transport; the marker block still
        // distinguishes this havoc from ordinary memory. The body can only
        // initialize more, so every automatic value that goes stays
        // initialized at the head and after the loop.
        let base = Some(intern_derivation_base(&mut self));
        self.forget_borrow_unprotected_values(scope, preserved_blocks, ledger, &[]);
        // The body may also have written bytes no value was cached for, and
        // a zero reading answers for exactly those.
        match mutable_ranges {
            Some(ranges) => {
                self.forget_zero_readings_under(ranges.iter().map(|range| &range.base().base))
            }
            None => self.forget_every_zero_reading(),
        }
        // Interned histories may share a variable and write footprint only
        // when they retain the same frame. The persistent frame identity is
        // already maintained; naming it does not enumerate its resources.
        let marker = kept_by_function.as_ref().map_or_else(
            || format!("havoc:{}", variable.0),
            |kept| format!("havoc:{}:{}", variable.0, kept.identity()),
        );
        std::sync::Arc::make_mut(&mut self.blocks).insert(
            marker.into(),
            MemoryBlock::new(mutable_ranges.map_or(0, memory_havoc_write_set_fingerprint)),
        );
        if let Some(base) = base {
            record_memory_derivation(
                &mut self,
                MemoryDerivation::LoopHavoc {
                    base,
                    variable,
                    mutable_ranges: mutable_ranges.map(|ranges| ranges.to_vec()),
                    kept_by_function,
                },
            );
        }
        self
    }

    /// Forgets every cached value nothing protects from a write through an
    /// arbitrary reachable pointer: the one rule of the loop head and of the
    /// interface join ([`borrow_preserving_havoc_keeps_cell`]), asked of cells
    /// and typed union views alike. The loop head skips private scalar
    /// cells when its caller has already abstracted direct assignments.
    ///
    /// `agreeing` are the arms of a join, and empty at a loop head. A cell
    /// every arm caches with the same value is a reading each arm's memory
    /// already gives, so it is a reading of their join and stays; so does a
    /// run every arm holds unchanged. Only plain cells stay this way: a typed
    /// union view, and a cell a union overlays, go by the borrow rule alone.
    /// The work is unchanged: one lookup per arm for each value visited.
    fn forget_borrow_unprotected_values(
        &mut self,
        scope: ForgetScope<'_>,
        preserved_blocks: &dyn BlockMembership,
        ledger: Option<&crate::kernel::borrows::BorrowLedger>,
        agreeing: &[&SymbolicMemory],
    ) {
        let union_widths = union_overlay_widths(self);
        let arm_overlays = agreeing
            .iter()
            .map(|memory| union_overlay_widths(memory))
            .collect::<Vec<_>>();
        self.forget_cached_values(
            scope,
            |pointer, value| {
                // A view is asked by its own width; a cell by the widest
                // overlay at its address as well, so the borrow question
                // covers every byte it can be read as.
                let width = match value {
                    CachedValue::Cell(_) => union_widths.get(pointer).copied().unwrap_or(0),
                    CachedValue::UnionView(..) => 0,
                };
                if let CachedValue::Cell(cell) = value
                    && !agreeing.is_empty()
                    && agreeing
                        .iter()
                        .zip(&arm_overlays)
                        .all(|(memory, overlays)| {
                            !overlays.contains_key(pointer)
                                && memory
                                    .cells
                                    .concrete()
                                    .get(pointer)
                                    .map(|value| value.native())
                                    == Some(cell)
                        })
                {
                    return CachedValueFate::Kept;
                }
                if borrow_preserving_havoc_keeps_cell(
                    pointer,
                    value.byte_width().max(width),
                    preserved_blocks,
                    ledger,
                ) {
                    CachedValueFate::Kept
                } else {
                    CachedValueFate::Forgotten
                }
            },
            |run| {
                // A run every arm holds, holes and all, answers the same
                // reads in each of them, so the join keeps it whole. This
                // keeps more than the per-cell rule above, which looks only
                // at concrete cells so that it never spreads a run out.
                if !agreeing.is_empty() && agreeing.iter().all(|memory| memory.cells.holds_run(run))
                {
                    return (SlotSet::All, crate::kernel::primitives::RuleAnswer::Sound);
                }
                borrow_preserving_havoc_keeps_run(run, preserved_blocks, ledger)
            },
        );
    }

    /// Drops every zero reading, for a transition that may have written any
    /// allocation.
    fn forget_every_zero_reading(&mut self) {
        if self.heap.zeroed_allocations.len() == 0 && self.heap.zeroed_prefix_allocations.is_empty()
        {
            return;
        }
        let heap = std::sync::Arc::make_mut(&mut self.heap);
        heap.zeroed_allocations = HashedOrdSet::new();
        heap.zeroed_prefix_allocations = HashedOrdMap::new();
    }

    /// Forgets branch-local cell values and constructs the conservative heap
    /// state exported by an interface join. A branch may retire an allocation
    /// while its sibling keeps it live; the join must retain the potential
    /// live allocation so a guarded resource can decide whether the
    /// continuation may use it. Tombstones are unioned because a continuation
    /// must reject an alias if any incoming arm has ended its automatic
    /// lifetime.
    ///
    /// This is deliberately separate from loop havoc. The joined heap is the
    /// union of potential live allocations, so making the transition look like
    /// a loop havoc would record a false memory-DAG derivation. The resulting
    /// state is a history barrier instead: no load from before the
    /// branch is transported across it. What survives is a value every arm
    /// still caches for the same cell, kept as a cell of the joined state,
    /// and whatever the interface states as a fact.
    #[cfg(test)]
    pub(in crate::kernel) fn with_interface_memory_havoc(
        self,
        variable: Variable,
        preserved_blocks: &dyn BlockMembership,
        sibling_memories: &[&SymbolicMemory],
    ) -> Result<Self, String> {
        self.with_interface_memory_havoc_preserving_borrows(
            variable,
            preserved_blocks,
            sibling_memories,
            None,
        )
    }

    pub(in crate::kernel) fn with_interface_memory_havoc_preserving_borrows(
        mut self,
        variable: Variable,
        preserved_blocks: &dyn BlockMembership,
        sibling_memories: &[&SymbolicMemory],
        ledger: Option<&crate::kernel::borrows::BorrowLedger>,
    ) -> Result<Self, String> {
        let mut incoming = std::iter::once(&self)
            .chain(sibling_memories.iter().copied())
            .map(intern_memory_ref)
            .collect::<Vec<_>>();
        incoming.sort_by_key(SharedMemory::arena_id);
        incoming.dedup();
        let Some(first) = sibling_memories.first() else {
            return Err("an interface memory join has no sibling states".to_string());
        };

        // Every merge below starts from the first arm's collection and
        // visits only the entries on which another arm differs from it. The
        // arms share what neither touched, so the work is their changes.
        let others = &sibling_memories[1..];
        let blocks = first
            .blocks
            .union_of_arms(others.iter().map(|memory| &*memory.blocks))
            .map_err(|block| {
                format!("interface arms disagree on the size of memory block {block:?}")
            })?;
        let ended_local_blocks = union_of_arm_sets(
            &first.forgotten.ended_local_blocks,
            others
                .iter()
                .map(|memory| &memory.forgotten.ended_local_blocks),
        );
        let ended_addressable_local_blocks = union_of_arm_sets(
            &first.forgotten.ended_addressable_local_blocks,
            others
                .iter()
                .map(|memory| &memory.forgotten.ended_addressable_local_blocks),
        );
        let live_allocations = union_of_arm_maps(
            &first.heap.live_allocations,
            others.iter().map(|memory| &memory.heap.live_allocations),
        )
        .map_err(|base| {
            format!("interface arms disagree on the size of heap allocation {base:?}")
        })?;
        let deallocated_allocations = union_of_arm_maps(
            &first.heap.deallocated_allocations,
            others
                .iter()
                .map(|memory| &memory.heap.deallocated_allocations),
        )
        .map_err(|base| {
            format!("interface arms disagree on the size of freed heap allocation {base:?}")
        })?;

        let pending_allocations = first.heap.pending_allocations.clone();
        if sibling_memories
            .iter()
            .any(|memory| memory.heap.pending_allocations != pending_allocations)
        {
            return Err("interface arms disagree on pending heap allocations".to_string());
        }
        let pending_object_classes = first.heap.pending_object_classes.clone();
        if sibling_memories
            .iter()
            .any(|memory| memory.heap.pending_object_classes != pending_object_classes)
        {
            return Err("interface arms disagree on pending heap object classes".to_string());
        }
        let pending_reallocations = first.heap.pending_reallocations.clone();
        if sibling_memories
            .iter()
            .any(|memory| memory.heap.pending_reallocations != pending_reallocations)
        {
            return Err("interface arms disagree on pending heap reallocations".to_string());
        }
        // An effective type survives the join only where every arm agrees;
        // an entry whose cell the join forgets is unconfirmed anyway.
        let effective_types = if others
            .iter()
            .all(|memory| memory.heap.effective_types == first.heap.effective_types)
        {
            first.heap.effective_types.clone()
        } else {
            super::HeapEffectiveTypes::default()
        };

        let uninitialized_objects = union_of_arm_maps(
            &first.heap.uninitialized_objects,
            others
                .iter()
                .map(|memory| &memory.heap.uninitialized_objects),
        )
        .map_err(|base| format!("interface arms disagree on unwritten object size at {base:?}"))?;

        let uninitialized_allocations = union_of_arm_sets(
            &first.heap.uninitialized_allocations,
            others
                .iter()
                .map(|memory| &memory.heap.uninitialized_allocations),
        );

        // A byte is definitely initialized at the join only when every
        // incoming arm initialized it: in the arm's record, or as an
        // automatic cell the arm still caches (the cell is its own evidence
        // until the join forgets it). This carries initialization, not a
        // value, so it remains useful after the join's conservative value
        // havoc. Cells of preserved blocks survive the join as cells.
        let arm_initialized = |memory: &SymbolicMemory| {
            let mut record = memory.heap.initialized.clone();
            let mut visited = 0usize;
            for (pointer, value) in local_block_entries(memory.cells.logical()) {
                visited += 1;
                if !preserved_blocks.contains_block(&pointer.base) {
                    record.record(pointer, value.byte_width());
                }
            }
            for ((pointer, program_type), _) in local_block_entries(&memory.union_cells) {
                visited += 1;
                if !preserved_blocks.contains_block(&pointer.base) {
                    record.record(pointer, program_type.byte_width());
                }
            }
            crate::instrumentation::record_deterministic_work(visited);
            record
        };
        let mut initialized = arm_initialized(first);
        for memory in &sibling_memories[1..] {
            initialized = initialized.intersection(&arm_initialized(memory));
        }

        // A zero marker is a value guarantee, so it is retained only when
        // every arm provides it. (The uninitialized marker above is instead
        // unioned because a possibly-uninitialized read must remain unsafe.)
        let mut zeroed_allocations = first.heap.zeroed_allocations.clone();
        for memory in others {
            for base in first
                .heap
                .zeroed_allocations
                .symmetric_difference(&memory.heap.zeroed_allocations)
            {
                zeroed_allocations.remove(base);
            }
        }
        let mut zeroed_prefix_allocations = HashedOrdMap::new();
        // An allocation gets a zeroed prefix only where some arm has less
        // than the whole of it zeroed. When every arm has the same whole
        // allocations zeroed and none has a prefix, there is none to find.
        let arms_have_zeroed_prefixes = sibling_memories.iter().any(|memory| {
            !memory.heap.zeroed_prefix_allocations.is_empty()
                || memory.heap.zeroed_allocations != first.heap.zeroed_allocations
        });
        for base in live_allocations
            .keys()
            .filter(|_| arms_have_zeroed_prefixes)
        {
            let prefixes = sibling_memories
                .iter()
                .map(|memory| {
                    if memory.heap.zeroed_allocations.contains(base) {
                        memory
                            .heap
                            .live_allocations
                            .get(base)
                            .map(AllocationSize::bytes)
                    } else {
                        memory.heap.zeroed_prefix_allocations.get(base)
                    }
                })
                .collect::<Option<Vec<_>>>();
            let Some(prefixes) = prefixes else {
                continue;
            };
            let Some(prefixes) = prefixes
                .into_iter()
                .map(OldMachineTerm::as_const)
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            if sibling_memories
                .iter()
                .any(|memory| !memory.heap.zeroed_allocations.contains(base))
            {
                zeroed_allocations.remove(base);
                zeroed_prefix_allocations.insert(
                    base.clone(),
                    OldMachineTerm::constant(
                        prefixes.into_iter().min().expect("nonempty interface arms"),
                    ),
                );
            }
        }
        let zeroed_pending_allocations = first.heap.zeroed_pending_allocations.clone();
        if sibling_memories
            .iter()
            .any(|memory| memory.heap.zeroed_pending_allocations != zeroed_pending_allocations)
        {
            return Err("interface arms disagree on zeroed pending heap allocations".to_string());
        }

        // Whole-memory by design: a join merges every sibling's blocks and
        // heap collections above, and forgets every cached value that
        // nothing preserves and the arms do not agree on, cells and union
        // views alike. The heap it records along the way is replaced below
        // by the arms' join, which is the one that decides initialization.
        // With no typed union view in play, the cells are settled from the
        // arms' differences alone. A union view is forgotten whatever the
        // arms agree on, and a cell under one goes with it, so a state
        // that holds any takes the whole-map pass.
        let by_difference = self.union_cells.is_empty()
            && sibling_memories
                .iter()
                .all(|memory| memory.union_cells.is_empty());
        let differing_blocks = if by_difference {
            let other_cells = sibling_memories
                .iter()
                .map(|memory| &*memory.cells)
                .collect::<Vec<_>>();
            Some(
                std::sync::Arc::make_mut(&mut self.cells).retain_agreed_with(
                    &other_cells,
                    |pointer, value| {
                        borrow_preserving_havoc_keeps_cell(
                            pointer,
                            value.byte_width(),
                            preserved_blocks,
                            ledger,
                        )
                    },
                    |run| borrow_preserving_havoc_keeps_run(run, preserved_blocks, ledger),
                ),
            )
        } else {
            self.forget_borrow_unprotected_values(
                ForgetScope::Everywhere,
                preserved_blocks,
                ledger,
                sibling_memories,
            );
            None
        };
        // A zero reading is kept only where every arm has it, but an arm can
        // have it beside a value it wrote over the zeros, and that value is
        // forgotten here. So a reading goes wherever *any* arm caches a value
        // the join forgets, which is also what keeps every arm's abstraction
        // the same one.
        let forgotten_value_blocks = |memory: &SymbolicMemory| {
            if zeroed_allocations.len() == 0 && zeroed_prefix_allocations.is_empty() {
                return BTreeSet::new();
            }
            let mut blocks = BTreeSet::new();
            let mut visited = 0usize;
            let union_widths = union_overlay_widths(memory);
            for (pointer, value) in memory.cells.logical().iter() {
                visited += 1;
                if !borrow_preserving_havoc_keeps_cell(
                    pointer,
                    value
                        .byte_width()
                        .max(union_widths.get(pointer).copied().unwrap_or(0)),
                    preserved_blocks,
                    ledger,
                ) {
                    blocks.insert(pointer.base.clone());
                }
            }
            for ((pointer, program_type), _) in memory.union_cells.iter() {
                visited += 1;
                if !borrow_preserving_havoc_keeps_cell(
                    pointer,
                    program_type.byte_width(),
                    preserved_blocks,
                    ledger,
                ) {
                    blocks.insert(pointer.base.clone());
                }
            }
            crate::instrumentation::record_deterministic_work(visited);
            blocks
        };
        let forgotten_blocks = match differing_blocks {
            // The blocks in which some arm holds a value the join forgets
            // are the blocks in which the arms differ.
            Some(blocks) => blocks,
            None => sibling_memories
                .iter()
                .flat_map(|memory| forgotten_value_blocks(memory))
                .collect::<BTreeSet<_>>(),
        };
        let mut blocks = blocks;
        blocks.insert(format!("havoc:{}", variable.0).into(), MemoryBlock::new(0));
        self.blocks = std::sync::Arc::new(blocks);
        let forgotten = std::sync::Arc::make_mut(&mut self.forgotten);
        forgotten.ended_local_blocks = ended_local_blocks;
        forgotten.ended_addressable_local_blocks = ended_addressable_local_blocks;
        // A forget mark says this state is some earlier one with cached
        // values dropped and the memory itself unchanged. The joined memory
        // is no arm's memory: it is their abstraction, named by its own
        // fresh havoc block above. Keeping an arm's mark would also make the
        // abstraction depend on which arm it was computed from, so arms that
        // forgot from different states on the way could never rejoin.
        forgotten.forgotten_from = None;
        forgotten.join_inputs = incoming
            .iter()
            .map(|memory| ForgottenFrom {
                content_hash: memory_content_hash(memory.memory()),
                arena_id: memory.arena_id(),
            })
            .collect();
        self.heap = std::sync::Arc::new(HeapMemory {
            live_allocations,
            deallocated_allocations,
            pending_allocations,
            pending_object_classes,
            uninitialized_allocations,
            uninitialized_objects,
            initialized,
            zeroed_allocations,
            zeroed_prefix_allocations,
            zeroed_pending_allocations,
            pending_reallocations,
            effective_types,
        });
        self.forget_zero_readings_under(forgotten_blocks.iter());
        record_memory_derivation(
            &mut self,
            MemoryDerivation::BranchJoin {
                base: incoming[0].clone(),
                incoming,
            },
        );
        Ok(self)
    }

    /// A runtime operation writes the declared storage itself, including
    /// automatic storage. Ordinary contract calls separately preserve their
    /// caller-local variable slots; that convention does not apply here.
    pub(in crate::kernel) fn with_storage_memory_havoc(
        self,
        variable: Variable,
        mutable_ranges: &[MemoryRange],
        assumptions: &PureFactContext,
    ) -> Self {
        self.with_memory_havoc(
            variable,
            mutable_ranges,
            assumptions,
            None,
            false,
            None,
            None,
        )
    }

    pub(in crate::kernel) fn with_call_memory_havoc(
        self,
        variable: Variable,
        mutable_ranges: &[MemoryRange],
        assumptions: &PureFactContext,
        kept: Option<&CallKeptOwnership>,
    ) -> Self {
        self.with_call_memory_havoc_with_copy(variable, mutable_ranges, assumptions, kept, None)
    }

    pub(in crate::kernel) fn with_call_memory_havoc_with_copy(
        self,
        variable: Variable,
        mutable_ranges: &[MemoryRange],
        assumptions: &PureFactContext,
        kept: Option<&CallKeptOwnership>,
        copy: Option<&RepresentationCopyRange>,
    ) -> Self {
        self.with_bounded_call_memory_havoc(variable, mutable_ranges, assumptions, kept, copy, None)
    }

    /// [`Self::with_call_memory_havoc_with_copy`] for a call whose writes all
    /// lie inside `resource_bound`, which its step records.
    pub(in crate::kernel) fn with_bounded_call_memory_havoc(
        self,
        variable: Variable,
        mutable_ranges: &[MemoryRange],
        assumptions: &PureFactContext,
        kept: Option<&CallKeptOwnership>,
        copy: Option<&RepresentationCopyRange>,
        resource_bound: Option<std::sync::Arc<Resource>>,
    ) -> Self {
        self.with_memory_havoc(
            variable,
            mutable_ranges,
            assumptions,
            kept,
            true,
            copy,
            resource_bound,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn with_memory_havoc(
        mut self,
        variable: Variable,
        mutable_ranges: &[MemoryRange],
        assumptions: &PureFactContext,
        kept: Option<&CallKeptOwnership>,
        preserve_local_slots: bool,
        copy: Option<&RepresentationCopyRange>,
        resource_bound: Option<std::sync::Arc<Resource>>,
    ) -> Self {
        let base = Some(intern_derivation_base(&mut self));
        let candidates = call_havoc_candidates(mutable_ranges);
        // Cells and typed union views by one rule: a view is the
        // authoritative answer to an exact typed load, so one the callee may
        // have overwritten goes exactly as a cell does
        // (`mdtests/call_havoc_drops_a_union_member_view.md`). A callee can
        // only initialize more, so the automatic values that go stay
        // initialized.
        let exact_write = call_havoc_exact_byte_write(mutable_ranges);
        let cells_kept = exact_write
            .as_ref()
            .map_or_else(Vec::new, |(pointer, bytes)| {
                crate::kernel::reasoning::store_gap::store_gap_kept_ranges(
                    pointer,
                    *bytes,
                    assumptions,
                )
            });
        let selected = self.cells.call_havoc_selection(
            kept.map(|kept| &kept.residual),
            &candidates,
            &cells_kept,
        );
        let scope = match selected.as_ref() {
            Some(selected) => ForgetScope::Ordered {
                candidates: &candidates,
                selected: &selected.cells,
                cells_kept: &[],
                runs: selected.runs.as_deref(),
            },
            None => ForgetScope::candidates(&candidates),
        };
        self.forget_cached_values(
            scope,
            |pointer, value| match call_havoc_keeps_cell(
                pointer,
                value.value(),
                mutable_ranges,
                assumptions,
                kept,
                preserve_local_slots,
            ) {
                CallHavocCellRule::Separate => CachedValueFate::Kept,
                // The cached value is dropped as before; the edge records
                // the member that holds it, and a load after the call is
                // named across the edge at its pre-call value.
                CallHavocCellRule::KeptByCaller => CachedValueFate::Forgotten,
                CallHavocCellRule::Dropped => CachedValueFate::Forgotten,
            },
            |run| match call_havoc_run_window(exact_write.as_ref(), run) {
                Some((low, high)) => (SlotSet::PerSlotIn(low, high), RuleAnswer::Exact),
                None => ask_every_slot(run),
            },
        );
        if let (Some(copy), Some(before)) = (copy, &base) {
            self.replace_initialization_for_representation_copy(before, copy);
        }
        let kept_ranges = call_havoc_kept_ranges(kept);
        self.forget_zeroed_allocations_written_by(mutable_ranges, assumptions);
        std::sync::Arc::make_mut(&mut self.blocks).insert(
            format!("call-havoc:{}", variable.0).into(),
            MemoryBlock::new(memory_havoc_write_set_fingerprint(mutable_ranges)),
        );
        // Keep the legacy marker's semantic shape and add a collision-free
        // structural key for the checked write set, and for the memory the
        // caller kept owning. This key is intentionally not named as a havoc
        // marker: canonical load states must continue to treat the
        // call-havoc edge as the only global memory barrier.
        std::sync::Arc::make_mut(&mut self.blocks).insert(
            call_write_set_marker(variable.0, mutable_ranges, kept_ranges.as_ref()),
            MemoryBlock::new(0),
        );
        if let Some(base) = base {
            record_memory_derivation(
                &mut self,
                MemoryDerivation::CallHavoc {
                    base,
                    variable,
                    mutable_ranges: mutable_ranges.to_vec(),
                    kept_by_caller: kept_ranges,
                    resource_bound,
                },
            );
        }
        self
    }

    /// A representation copy replaces the destination's initialization,
    /// including holes. Use the pre-call state even when the two spans share
    /// one block. The ordinary call edge already describes the write, so
    /// publish this metadata as part of that edge.
    fn replace_initialization_for_representation_copy(
        &mut self,
        source_memory: &SymbolicMemory,
        copy: &RepresentationCopyRange,
    ) {
        let source_start = copy.source.offset.as_const().expect("exact source");
        let source_end = source_start + i64::from(copy.bytes);
        let destination_start = copy
            .destination
            .offset
            .as_const()
            .expect("exact destination");
        let at = |offset| copy.source.with_offset(AddressOffset::constant(offset));
        let mut initialized = self.heap.initialized.clone();
        initialized
            .copy_exact_range_from(
                &source_memory.heap.initialized,
                &copy.source,
                &copy.destination,
                copy.bytes,
            )
            .expect("checked representation copy range");
        initialized.forget_symbolic_offsets(&copy.destination.base);
        let mut record = |start: i64, bytes| {
            let address = copy.destination.with_offset(AddressOffset::constant(
                destination_start + (start - source_start),
            ));
            initialized.record(&address, bytes);
        };
        // A cell can establish initialization even if it has no separate
        // record, or if the copy cuts through it and cannot retain its type.
        let first = source_memory
            .cells
            .range(at(i64::MIN)..at(source_start))
            .next_back()
            .map_or_else(|| at(source_start), |(address, _)| address.clone());
        crate::instrumentation::record_deterministic_work(1);
        for (address, value) in source_memory.cells.range(first..at(source_end)) {
            crate::instrumentation::record_deterministic_work(1);
            let offset = address.offset.as_const().expect("constant cell range");
            let start = offset.max(source_start);
            let end = offset
                .saturating_add(i64::from(value.byte_width()))
                .min(source_end);
            if start < end {
                record(start, u32::try_from(end - start).expect("clipped cell"));
            }
        }
        let heap = Arc::make_mut(&mut self.heap);
        heap.initialized = initialized;
        if !copy.destination.base.is_local_block() {
            // A zeroed allocation, for example, may not already have an
            // unwritten marker. The copy creates an initialization history
            // for the destination span even in that case.
            let width = heap
                .uninitialized_objects
                .get(&copy.destination)
                .copied()
                .unwrap_or(0)
                .max(copy.bytes);
            heap.uninitialized_objects
                .insert(copy.destination.clone(), width);
        }
    }

    /// Commit a checked write that leaves a partial byte. No whole-byte
    /// value may be published in the cell cache or on the memory edge.
    pub(in crate::kernel) fn store_partial_byte(
        mut self,
        pointer: Address,
        mask: u8,
        value: ProgramValue,
        assumptions: &PureFactContext,
    ) -> Self {
        let base = intern_derivation_base(&mut self);
        if let Some((mut prepared, lost_knowledge)) =
            self.prepare_store_cache(&pointer, 1, assumptions, None)
        {
            if lost_knowledge {
                prepared.mark_forgotten_from(&base);
            }
            self = prepared;
        }
        Arc::make_mut(&mut self.heap)
            .initialized
            .set_partial(pointer.clone(), mask, Some(value));
        record_memory_derivation(
            &mut self,
            MemoryDerivation::RepresentationWrite {
                base,
                pointer,
                bytes: 1,
            },
        );
        self
    }

    /// Copy the named fields of a local bit-field record from one snapshot.
    /// Assignment carries the source members, including unwritten fields.
    /// It does not guarantee that a source padding bit is copied.
    pub(in crate::kernel) fn copy_local_bit_field_record(
        mut self,
        source: &Address,
        destination: &Address,
        bytes: u32,
        field_bytes: &[(u32, std::num::NonZeroU8)],
        fields: &[AggregateField],
    ) -> Result<Self, UndefinedBehavior> {
        if !source.base.is_local_block()
            || !destination.base.is_local_block()
            || !self.access_in_bounds(source, bytes)
            || !self.access_in_bounds(destination, bytes)
            || self.is_read_only_block(&destination.base)
        {
            return Err(UndefinedBehavior::InvalidMemory);
        }
        let snapshot = self.clone();
        let base = intern_derivation_base(&mut self);
        let context = PureFactContext::new();
        if let Some((mut prepared, lost_knowledge)) =
            self.prepare_store_cache(destination, bytes, &context, None)
        {
            if lost_knowledge {
                prepared.mark_forgotten_from(&base);
            }
            self = prepared;
        }
        let initialized = &mut Arc::make_mut(&mut self.heap).initialized;
        initialized.forget(destination, bytes);
        initialized.forget_symbolic_offsets(&destination.base);
        for &(offset, members) in field_bytes {
            crate::instrumentation::record_deterministic_work(1);
            let from = source.offset_by_bytes(offset);
            let to = destination.offset_by_bytes(offset);
            let full =
                crate::kernel::eval::known_integer_byte(&snapshot, &from, Some(ByteOrder::Little));
            let source_initialization = &snapshot.heap.initialized;
            let mask = members.get()
                & if full.is_some() {
                    u8::MAX
                } else {
                    source_initialization.mask_at(&from)
                };
            let value = full.or_else(|| {
                let ProgramValue::UInt8(value) =
                    source_initialization.partial_byte(&from)?.value.as_ref()?
                else {
                    return None;
                };
                Some(value.clone())
            });
            match mask {
                0 => {}
                u8::MAX => {
                    initialized.record(&to, 1);
                    if let Some(value) = value {
                        Arc::make_mut(&mut self.cells).insert(to, ProgramValue::UInt8(value));
                    }
                }
                _ => {
                    let value = value.map(|value| {
                        ProgramValue::UInt8(crate::kernel::eval::mask_byte(value, mask))
                    });
                    initialized.set_partial(to, mask, value);
                }
            }
        }
        for field in fields {
            let width = field.program_type().byte_width();
            let from = source.offset_by_layout(field.offset());
            let to = destination.offset_by_layout(field.offset());
            initialized
                .copy_exact_range_from(&snapshot.heap.initialized, &from, &to, width)
                .expect("checked local member range");
            let start = from.offset.as_const().expect("exact local member");
            for (address, value) in snapshot
                .cells
                .concrete()
                .range(from.clone()..from.offset_by_bytes(width))
            {
                crate::instrumentation::record_deterministic_work(1);
                let offset = address.offset.as_const().expect("exact cell offset") - start;
                let relative = u32::try_from(offset).expect("cell starts within the member");
                if value.byte_width() <= width - relative {
                    let target = to.offset_by_bytes(relative);
                    initialized.record(&target, value.byte_width());
                    Arc::make_mut(&mut self.cells).insert_retained(target, value.clone());
                }
            }
        }
        record_memory_derivation(
            &mut self,
            MemoryDerivation::RepresentationWrite {
                base,
                pointer: destination.clone(),
                bytes,
            },
        );
        Ok(self)
    }

    /// Checks that `self` is exactly the cell-and-marker result produced by a
    /// call havoc from `before`. This is deliberately a structural producer
    /// check rather than a second alias approximation: erased cells are
    /// accepted only when the endpoint has the call-havoc shape and the same
    /// conservative retention rule as [`Self::with_call_memory_havoc`].
    pub(in crate::kernel) fn matches_call_memory_havoc_result(
        &self,
        before: &Self,
        mutable_ranges: &[MemoryRange],
        assumptions: &PureFactContext,
        kept: Option<&CallKeptOwnership>,
    ) -> bool {
        if self.blocks.len() != before.blocks.len() + 2 {
            return false;
        }
        // `self.blocks` must be `before.blocks` plus exactly two new blocks.
        // The maps share every unchanged subtree, so the diff walks only the
        // two inserted paths.
        let mut added_blocks = Vec::new();
        for change in before.blocks.diff(&self.blocks) {
            let HashedOrdMapChange::Added(block) = change else {
                return false;
            };
            let Some(contents) = self.blocks.get(block) else {
                return false;
            };
            added_blocks.push((block, contents));
        }
        let Some((marker, marker_block)) = added_blocks
            .iter()
            .find(|(block, _)| block.is_call_havoc_block())
        else {
            return false;
        };
        let Some(variable) = marker
            .strip_prefix("call-havoc:")
            .and_then(|variable| variable.parse::<u64>().ok())
        else {
            return false;
        };

        // The producer's rule, over the same candidates: every cell outside
        // them is kept by `call_havoc_keeps_cell`, so the expected result is
        // `before` without the candidates the rule drops, and the comparison
        // walks only the paths the two states do not share.
        let candidates = call_havoc_candidates(mutable_ranges);
        let mut visited = 0usize;
        let mut dropped_cells = Vec::new();
        let mut dropped_initialized = Vec::new();
        let exact_write = call_havoc_exact_byte_write(mutable_ranges);
        let cells_kept = exact_write
            .as_ref()
            .map_or_else(Vec::new, |(pointer, bytes)| {
                crate::kernel::reasoning::store_gap::store_gap_kept_ranges(
                    pointer,
                    *bytes,
                    assumptions,
                )
            });
        let selected = before.cells.call_havoc_selection(
            kept.map(|kept| &kept.residual),
            &candidates,
            &cells_kept,
        );
        let entries = before.cells.candidate_logical_entries_selected(
            &candidates,
            selected.as_ref().map(|selected| selected.cells.as_slice()),
            selected
                .as_ref()
                .and_then(|selected| selected.runs.as_deref()),
            |run| call_havoc_run_window(exact_write.as_ref(), run),
        );
        for (pointer, value) in entries {
            visited += 1;
            match call_havoc_keeps_cell(&pointer, &value, mutable_ranges, assumptions, kept, true) {
                CallHavocCellRule::Separate => {}
                CallHavocCellRule::KeptByCaller => {
                    dropped_initialized.push((pointer.clone(), value.byte_width()));
                    dropped_cells.push(pointer);
                }
                CallHavocCellRule::Dropped => {
                    dropped_initialized.push((pointer.clone(), value.byte_width()));
                    dropped_cells.push(pointer);
                }
            }
        }
        let dropped_cells = dropped_cells.iter().collect::<Vec<_>>();
        let mut dropped_union_cells = Vec::new();
        for (key, value) in candidates.entries(&before.union_cells) {
            visited += 1;
            match call_havoc_keeps_cell(
                &key.0,
                value.native(),
                mutable_ranges,
                assumptions,
                kept,
                true,
            ) {
                CallHavocCellRule::Separate => {}
                CallHavocCellRule::KeptByCaller => {
                    dropped_initialized.push((key.0.clone(), key.1.byte_width()));
                    dropped_union_cells.push(key);
                }
                CallHavocCellRule::Dropped => {
                    dropped_initialized.push((key.0.clone(), key.1.byte_width()));
                    dropped_union_cells.push(key);
                }
            }
        }
        crate::instrumentation::record_deterministic_work(visited);
        // The producer's heap: `before`'s, with the automatic values it
        // dropped recorded initialized, and without the zero readings under
        // a dropped value or the write set ([`SymbolicMemory::forget_cached_values`]).
        let mut expected = before.clone();
        expected.record_dropped_initialized_cells(&dropped_initialized);
        if !before.heap.initialized.partial_map().is_empty() {
            Arc::make_mut(&mut expected.heap)
                .initialized
                .forget_partial_values(Some((&candidates, &[])), |address, value| {
                    matches!(
                        call_havoc_keeps_cell(
                            address,
                            value,
                            mutable_ranges,
                            assumptions,
                            kept,
                            true
                        ),
                        CallHavocCellRule::Separate
                    )
                });
        }
        expected.forget_zero_readings_under(
            dropped_initialized.iter().map(|(pointer, _)| &pointer.base),
        );
        expected.forget_zeroed_allocations_written_by(mutable_ranges, assumptions);
        if !self.heap.eq_relative_to(&expected.heap, &before.heap) {
            return false;
        }
        let kept_ranges = call_havoc_kept_ranges(kept);
        let write_set_marker =
            call_write_set_marker(variable, mutable_ranges, kept_ranges.as_ref());
        if added_blocks.len() != 2
            || **marker_block
                != MemoryBlock::new(memory_havoc_write_set_fingerprint(mutable_ranges))
            || self.blocks.get(&write_set_marker) != Some(&MemoryBlock::new(0))
        {
            return false;
        }
        self.cells.is_without(&before.cells, &dropped_cells)
            && self
                .union_cells
                .is_without(&before.union_cells, &dropped_union_cells)
    }

    #[cfg(test)]
    pub(crate) fn with_seeded_cells(
        self,
        base: Address,
        element_width: u32,
        element_type: ProgramType,
        first: u32,
        count: u32,
        source: SharedMemory,
    ) -> Self {
        self.with_seeded_cells_at(
            base,
            element_width,
            element_type,
            first,
            count,
            ProgramPoint::unplaced(&source),
        )
    }

    /// Seeds the cells of elements `first..count` at `base`,
    /// `base + element_width`, …: each one the load of its own element in
    /// `source`, typed as `element_type` ([`cell_run_value`]). This is exactly
    /// `store` of each such value in element order, skipping every element
    /// that already holds a cell. It costs the same whatever `count` is: the cells are one [`CellRun`]
    /// and the stores one `CellsSeeded` edge.
    ///
    /// Two things a store does that a run does not represent are refused
    /// rather than approximated: displacing typed union views (the state
    /// holds some) and marking a live heap cell initialized (an allocation
    /// may hold the range). Those fall back to the stores themselves.
    ///
    /// A recorded source point is retained for each slot whose version the
    /// typed read selector can name.
    pub(crate) fn with_seeded_cells_at(
        mut self,
        base: Address,
        element_width: u32,
        element_type: ProgramType,
        first: u32,
        count: u32,
        source: ProgramPoint,
    ) -> Self {
        if first >= count {
            return self;
        }
        if !self.run_can_stand_for_cells_at(&base) {
            let run = CellRun::new_at(
                base,
                element_width,
                element_type,
                count,
                source,
                RunValueMode::Load,
                IndexIntervals::default(),
            );
            for index in first..count {
                let pointer = run.slot_pointer(index);
                if !matches!(self.load(&pointer), ExpressionOutcome::Value(_)) {
                    self = self.store(pointer, run.value(index));
                }
            }
            return self;
        }
        self.with_run_of_cells(
            base,
            element_width,
            element_type,
            first,
            count,
            source,
            RunValueMode::Load,
        )
    }

    /// [`Self::materialize_named_cell`] of each element `first..count` at
    /// `base`, `base + element_width`, …, whose value is the load of that
    /// element in `source` typed as `element_type` ([`cell_run_value`]), as
    /// one [`CellRun`]: the cells it leaves are exactly those, in element
    /// order, skipping every element that already holds a cell, at a cost
    /// that does not depend on `count`.
    ///
    /// A named cell is not a C write, so where `materialize_named_cell`
    /// declines some elements a run would not, the run is refused and
    /// `Err` hands the memory back unchanged for the caller's own cells: an
    /// automatic object's block (a named load does not initialize one), a
    /// heap block (fresh storage stays uninitialized), and, as for
    /// [`Self::with_seeded_cells_at`], a state with typed union views or a
    /// base that may lie in a live allocation.
    pub(crate) fn with_named_cell_run(
        self,
        base: Address,
        element_width: u32,
        element_type: ProgramType,
        first: u32,
        count: u32,
        source: ProgramPoint,
    ) -> Result<Self, Self> {
        if first >= count {
            return Ok(self);
        }
        if base.base.is_local_block()
            || matches!(base.base, AddressBase::Heap(_))
            || !self.run_can_stand_for_cells_at(&base)
        {
            return Err(self);
        }
        Ok(self.with_run_of_cells(
            base,
            element_width,
            element_type,
            first,
            count,
            source,
            RunValueMode::Load,
        ))
    }

    /// A store of `value` into each of the `count` elements of `element_type`
    /// at `base`, in element order, as one [`CellRun`] at a cost that does
    /// not depend on `count`: the known initial contents of static storage
    /// whose elements an initializer leaves at one value. The run's slots are
    /// exactly the cells the stores would leave, and one `CellsSeeded` edge
    /// stands for the stores.
    ///
    /// Where a run would not do what the stores do, `Err` hands the memory
    /// back unchanged for the caller's own stores: a block already holding a
    /// cell (a store overwrites it, where a run would keep it as a hole), an
    /// automatic or heap block (a store there marks initialization a run
    /// does not), and, as for [`Self::with_seeded_cells_at`], a state with
    /// typed union views or a base that may lie in a live allocation.
    pub(crate) fn with_constant_run(
        self,
        base: Address,
        element_type: ProgramType,
        count: u32,
        value: ProgramValue,
    ) -> Result<Self, Self> {
        if count == 0 {
            return Ok(self);
        }
        if base.base.is_local_block()
            || matches!(base.base, AddressBase::Heap(_))
            || value.program_type() != element_type
            || !self.run_can_stand_for_cells_at(&base)
            || AliasCandidates::only_block(&base.base)
                .entries(self.cells.concrete())
                .next()
                .is_some()
            || self.cells.runs_in_block(&base.base).next().is_some()
        {
            return Err(self);
        }
        let source = crate::kernel::intern_memory(SymbolicMemory::new());
        Ok(self.with_run_of_cells(
            base,
            element_type.byte_width(),
            element_type,
            0,
            count,
            ProgramPoint::unplaced(&source),
            RunValueMode::Constant(value),
        ))
    }

    /// The stores of one object's known initial contents, as one constant
    /// [`CellRun`] per entry of `runs`, at a cost of the runs rather than the
    /// cells they hold: the zero contents of an array of structs (one run per
    /// scalar field, stepping by the struct's size) or of an automatic array
    /// declared with an initializer. The runs' slots are exactly the cells
    /// the stores of each run's value into each of its slots would leave, and
    /// one `CellsSeeded` edge per run stands for them.
    ///
    /// The object at `base` must be fresh: its block holds no cell and no run
    /// yet, so no slot of a run is already a cell and the runs start with no
    /// hole. The caller builds the runs from one layout, so no two slots of
    /// them overlap; a slot's value is no wider than its run's step. Unlike
    /// [`Self::with_constant_run`] an automatic object's block is accepted:
    /// a store into a live local block records its cell and nothing else,
    /// and the declaration that just created the block is what calls this.
    /// A heap block (a store there marks the cell initialized), typed union
    /// views to displace, or a base in a live allocation are refused, and
    /// `Err` hands the memory back unchanged for the caller's own stores.
    pub(crate) fn with_constant_runs(
        self,
        base: &Address,
        runs: &[ConstantRun],
    ) -> Result<Self, Self> {
        if matches!(base.base, AddressBase::Heap(_))
            || !self.run_can_stand_for_cells_at(base)
            || AliasCandidates::only_block(&base.base)
                .entries(self.cells.concrete())
                .next()
                .is_some()
            || self.cells.runs_in_block(&base.base).next().is_some()
            || runs.iter().any(|run| {
                run.stride == 0 || (run.count > 1 && run.value.byte_width() > run.stride)
            })
        {
            return Err(self);
        }
        Ok(self.seed_fresh_declared_runs(base, runs))
    }

    /// Installs disjoint initial cells in an object just minted by a declaration.
    /// The declaration establishes freshness and supplies the typed run layout.
    pub(in crate::kernel) fn seed_fresh_declared_runs(
        mut self,
        base: &Address,
        runs: &[ConstantRun],
    ) -> Self {
        let source = crate::kernel::intern_memory(SymbolicMemory::new());
        for run in runs.iter().filter(|run| run.count > 0) {
            crate::instrumentation::record_deterministic_work(1);
            let run = CellRun::new_with_mode(
                base.offset_by_bytes(run.offset),
                run.stride,
                run.value.program_type(),
                run.count,
                source.clone(),
                RunValueMode::Constant(run.value.clone()),
                IndexIntervals::default(),
            );
            let derivation_base = intern_derivation_base(&mut self);
            std::sync::Arc::make_mut(&mut self.cells).add_run(run.clone());
            record_memory_derivation(
                &mut self,
                MemoryDerivation::CellsSeeded {
                    base: derivation_base,
                    run: std::sync::Arc::new(run),
                },
            );
        }
        self
    }

    /// Checked compact initialization of one fresh automatic scalar array.
    /// The caller has separately checked read/write authority and coercion.
    #[cfg(test)]
    pub(in crate::kernel) fn initialize_scalar_array(
        self,
        base: &Address,
        element_type: ProgramType,
        count: u32,
        value: ProgramValue,
        copy: bool,
    ) -> Result<Self, RuntimeError> {
        self.write_scalar_array_region(
            base,
            element_type,
            count,
            value,
            copy,
            true,
            &PureFactContext::new(),
        )
    }

    #[cfg(test)]
    pub(in crate::kernel) fn write_scalar_array_region(
        self,
        base: &Address,
        element_type: ProgramType,
        count: u32,
        value: ProgramValue,
        copy: bool,
        fresh: bool,
        assumptions: &PureFactContext,
    ) -> Result<Self, RuntimeError> {
        self.write_scalar_array_region_at(
            base,
            element_type,
            count,
            value,
            copy,
            fresh,
            assumptions,
            None,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::kernel) fn write_scalar_array_region_at(
        mut self,
        base: &Address,
        element_type: ProgramType,
        count: u32,
        value: ProgramValue,
        copy: bool,
        fresh: bool,
        assumptions: &PureFactContext,
        copy_source: Option<&ProgramPoint>,
    ) -> Result<Self, RuntimeError> {
        let bytes = count
            .checked_mul(element_type.byte_width())
            .filter(|bytes| *bytes <= i32::MAX as u32)
            .ok_or(RuntimeError::TypeMismatch)?;
        let state_copy = copy
            && matches!(&value, ProgramValue::Pointer(source) if
            !source.address().base.is_local_block()
            || self.cells.runs_in_block(&source.address().base)
                .any(|run| !matches!(run.value_mode(), RunValueMode::Constant(_))));
        if !base.base.is_local_block() || state_copy {
            return self.write_scalar_array_state_at(
                base,
                element_type,
                count,
                value,
                copy,
                fresh,
                assumptions,
                copy_source,
            );
        }
        let valid_region = |pointer: &Address| {
            pointer.base.is_local_block()
                && pointer.offset.as_const().is_some_and(|offset| {
                    offset >= 0
                        && offset % i64::from(element_type.byte_width()) == 0
                        && self
                            .block_size(&pointer.base)
                            .and_then(OldMachineTerm::as_const)
                            .is_some_and(|size| {
                                offset
                                    .checked_add(i64::from(bytes))
                                    .is_some_and(|end| end <= i64::from(size))
                            })
                })
        };
        if !element_type.supports_scalar_array_write(copy)
            || !valid_region(base)
            || !self.run_can_stand_for_cells_at(base)
            || (fresh
                && (!matches!(base.offset.view(), OffsetView::Constant(0))
                    || self
                        .block_size(&base.base)
                        .and_then(OldMachineTerm::as_const)
                        != Some(bytes)
                    || AliasCandidates::only_block(&base.base)
                        .entries(self.cells.concrete())
                        .next()
                        .is_some()
                    || self.cells.runs_in_block(&base.base).next().is_some()))
        {
            return Err(RuntimeError::FunctionContract(
                "scalar-array write requires a valid aligned local region; fresh initialization requires complete empty storage".into(),
            ));
        }
        // Capture represented values before changing the destination, including
        // overlapping copies. Constant spans stay compact; explicit lanes retain
        // their immutable values rather than referring back to mutable storage.
        let mut spans = Vec::new();
        let mut cells = Vec::new();
        if copy {
            let ProgramValue::Pointer(pointer) = &value else {
                return Err(RuntimeError::TypeMismatch);
            };
            let pointer = pointer.address();
            if !valid_region(pointer)
                || !self.run_can_stand_for_cells_at(pointer)
                || (bytes != 0 && !self.has_initialized_bytes_under(pointer, bytes, assumptions))
                || (fresh
                    && (!matches!(pointer.offset.view(), OffsetView::Constant(0))
                        || self
                            .block_size(&pointer.base)
                            .and_then(OldMachineTerm::as_const)
                            != Some(bytes)))
            {
                return Err(RuntimeError::FunctionContract(
                    "scalar-array copy requires a valid aligned initialized local source region"
                        .into(),
                ));
            }
            if count == 0 {
                return Ok(self);
            }
            let start = pointer.offset.as_const().unwrap();
            let end = start + i64::from(bytes);
            let width = i64::from(element_type.byte_width());
            let mut covered = IndexIntervals::default();
            let invalid = |reason: &str| {
                RuntimeError::FunctionContract(format!(
                    "scalar-array copy requires complete represented scalar values: {reason}"
                ))
            };
            for run in self.cells.runs_in_block(&pointer.base) {
                crate::instrumentation::record_deterministic_work(1);
                let Some(run_start) = run.base().offset.as_const() else {
                    return Err(invalid("symbolic run address"));
                };
                let run_end = i64::from(run.count())
                    .checked_mul(i64::from(run.element_width()))
                    .and_then(|bytes| run_start.checked_add(bytes))
                    .ok_or_else(|| invalid("run byte span overflow"))?;
                if run_end <= start || end <= run_start {
                    continue;
                }
                let RunValueMode::Constant(value) = run.value_mode() else {
                    return Err(invalid("unsupported run values"));
                };
                if run.element_type() != element_type
                    || value.program_type() != element_type
                    || run.element_width() != element_type.byte_width()
                    || (run_start - start) % width != 0
                {
                    return Err(invalid("run element type or alignment"));
                }
                for (low, high) in run.live_intervals().intervals() {
                    crate::instrumentation::record_deterministic_work(1);
                    let low = (run_start + i64::from(low) * width).max(start);
                    let high = (run_start + i64::from(high) * width).min(end);
                    if low < high {
                        let first = ((low - start) / width) as u32;
                        let last = ((high - start) / width) as u32;
                        covered.insert_range(first, last);
                        spans.push((first, last - first, value.clone()));
                    }
                }
            }
            let at = |offset| pointer.with_offset(AddressOffset::constant(offset));
            // Reject symbolic-address caches with one indexed lookup. Concrete
            // cells are visited only inside the selected byte region, plus the
            // bounded prefix where the widest scalar might overlap it.
            let max_width = crate::kernel::resource_tracker::widest_scalar_access_bytes();
            if self
                .cells
                .concrete()
                .range((
                    std::ops::Bound::Excluded(at(i64::MAX)),
                    std::ops::Bound::Unbounded,
                ))
                .next()
                .is_some_and(|(at, _)| at.base == pointer.base)
            {
                return Err(invalid("symbolic cached address"));
            }
            for (at, value) in self
                .cells
                .concrete()
                .range(at(start.saturating_sub(i64::from(max_width - 1)))..at(end))
            {
                crate::instrumentation::record_deterministic_work(1);
                let Some(offset) = at.offset.as_const() else {
                    return Err(invalid("nonconstant cell address"));
                };
                if offset + i64::from(value.byte_width()) <= start || end <= offset {
                    continue;
                }
                if offset < start
                    || offset + width > end
                    || (offset - start) % width != 0
                    || value.program_type() != element_type
                {
                    return Err(invalid(&format!(
                        "cell at byte {offset} with type {:?} does not fit {element_type:?} region {start}..{end}",
                        value.program_type()
                    )));
                }
                let index = ((offset - start) / width) as u32;
                covered.insert(index);
                cells.push((index, value.clone()));
            }
            if covered != IndexIntervals::full(count) {
                // A checked call may forget cached values of initialized
                // automatic storage. Copy the current state's unknown
                // lanes just as for external initialized storage, retaining
                // the represented lanes and the checks above.
                return self.write_scalar_array_state_at(
                    base,
                    element_type,
                    count,
                    value,
                    copy,
                    fresh,
                    assumptions,
                    copy_source,
                );
            }
        } else {
            if value.program_type() != element_type {
                return Err(RuntimeError::TypeMismatch);
            }
            spans.push((0, count, value));
        }
        if count == 0 {
            return Ok(self);
        }
        if !fresh {
            self = self.without_possible_aliasing_cells(base, bytes, assumptions);
        }
        let target_at = |index| {
            base.with_offset(AddressOffset::constant(
                base.offset.as_const().unwrap()
                    + i64::from(index) * i64::from(element_type.byte_width()),
            ))
        };
        for (first, length, value) in spans {
            let run = CellRun::new_with_mode(
                target_at(first),
                element_type.byte_width(),
                element_type,
                length,
                crate::kernel::intern_memory(SymbolicMemory::new()),
                RunValueMode::Constant(value),
                IndexIntervals::default(),
            );
            let derivation_base = intern_derivation_base(&mut self);
            std::sync::Arc::make_mut(&mut self.cells).add_run(run.clone());
            record_memory_derivation(
                &mut self,
                MemoryDerivation::CellsSeeded {
                    base: derivation_base,
                    run: std::sync::Arc::new(run),
                },
            );
        }
        for (index, value) in cells {
            self =
                self.store_retained_with_context(target_at(index), value.into_value(), assumptions);
        }
        Ok(self.with_initialized_object(base, bytes))
    }

    // Authority is checked by the statement executor. External argument
    // storage follows ordinary typed-load semantics: unknown initialized
    // bytes remain symbolic. Known automatic storage must be initialized.
    #[cfg(test)]
    pub(in crate::kernel) fn write_scalar_array_state(
        self,
        base: &Address,
        element: ProgramType,
        count: u32,
        value: ProgramValue,
        copy: bool,
        fresh: bool,
        assumptions: &PureFactContext,
    ) -> Result<Self, RuntimeError> {
        self.write_scalar_array_state_at(
            base,
            element,
            count,
            value,
            copy,
            fresh,
            assumptions,
            None,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::kernel) fn write_scalar_array_state_at(
        mut self,
        base: &Address,
        element: ProgramType,
        count: u32,
        value: ProgramValue,
        copy: bool,
        fresh: bool,
        assumptions: &PureFactContext,
        copy_source: Option<&ProgramPoint>,
    ) -> Result<Self, RuntimeError> {
        let bytes = count
            .checked_mul(element.byte_width())
            .filter(|bytes| *bytes <= i32::MAX as u32)
            .ok_or(RuntimeError::TypeMismatch)?;
        if !element.supports_scalar_array_write(copy) {
            return Err(RuntimeError::TypeMismatch);
        }
        if count == 0 {
            if (copy && !matches!(value, ProgramValue::Pointer(_)))
                || (!copy && value.program_type() != element)
            {
                return Err(RuntimeError::TypeMismatch);
            }
            return Ok(self);
        }
        let valid = |pointer: &Address| {
            let (stem, constant) = offset_stem_and_constant(&pointer.offset);
            let width = i64::from(element.byte_width());
            let aligned = constant % width == 0
                && match stem.map(|stem| stem.view()) {
                    None => true,
                    Some(OffsetView::Int32Scaled { byte_width, .. }) => byte_width % width == 0,
                    _ => false,
                };
            pointer != &Address::null()
                && constant.checked_add(i64::from(bytes)).is_some()
                && aligned
                && self.run_can_stand_for_cells_at(pointer)
                && if self.has_block(&pointer.base) {
                    self.access_in_bounds(pointer, bytes)
                } else {
                    matches!(
                        pointer.base,
                        AddressBase::ExternalArgument | AddressBase::ExternalObject(_)
                    )
                }
        };
        if !valid(base)
            || (fresh
                && (!base.base.is_local_block()
                    || !matches!(base.offset.view(), OffsetView::Constant(0))
                    || self
                        .block_size(&base.base)
                        .and_then(OldMachineTerm::as_const)
                        != Some(bytes)
                    || self.cells.runs_in_block(&base.base).next().is_some()
                    || AliasCandidates::only_block(&base.base)
                        .entries(self.cells.concrete())
                        .next()
                        .is_some()))
        {
            return Err(RuntimeError::FunctionContract("scalar-array retained_state requires valid aligned storage; fresh storage must be complete and empty".into()));
        }
        let mut captured_runs = Vec::new();
        let mut captured_cells = Vec::new();
        if copy {
            let ProgramValue::Pointer(pointer) = value else {
                return Err(RuntimeError::TypeMismatch);
            };
            let pointer = pointer.address();
            if !valid(pointer)
                || (pointer.base.is_local_block()
                    && !self.has_initialized_bytes_under(pointer, bytes, assumptions))
            {
                return Err(RuntimeError::FunctionContract(
                    "scalar-array state requires a valid initialized source region".into(),
                ));
            }
            let (stem, start) = offset_stem_and_constant(&pointer.offset);
            let width = i64::from(element.byte_width());
            let mut represented = IndexIntervals::default();
            for run in self.cells.runs_in_block(&pointer.base) {
                crate::instrumentation::record_deterministic_work(1);
                let (run_stem, run_start) = offset_stem_and_constant(&run.base().offset);
                if run_stem != stem {
                    continue;
                }
                let delta = run_start
                    .checked_sub(start)
                    .ok_or(RuntimeError::TypeMismatch)?;
                let end = delta
                    .checked_add(i64::from(run.count()) * i64::from(run.element_width()))
                    .ok_or(RuntimeError::TypeMismatch)?;
                if end <= 0 || delta >= i64::from(bytes) {
                    continue;
                }
                if run.element_type() != element
                    || run.element_width() != element.byte_width()
                    || delta % width != 0
                {
                    return Err(RuntimeError::TypeMismatch);
                }
                for (low, high) in run.live_intervals().intervals() {
                    crate::instrumentation::record_deterministic_work(1);
                    let low = (delta + i64::from(low) * width).max(0);
                    let high = (delta + i64::from(high) * width).min(i64::from(bytes));
                    if low >= high {
                        continue;
                    }
                    let first = (low / width) as u32;
                    let length = ((high - low) / width) as u32;
                    let source_index = ((low - delta) / width) as u32;
                    represented.insert_range(first, first + length);
                    let mode = match run.value_mode() {
                        RunValueMode::Constant(value) => RunValueMode::Constant(value.clone()),
                        RunValueMode::Copy { source_base } => RunValueMode::Copy {
                            source_base: source_base
                                .offset_by_bytes(source_index * element.byte_width()),
                        },
                        RunValueMode::Load => RunValueMode::Copy {
                            source_base: run.slot_pointer(source_index),
                        },
                    };
                    captured_runs.push(CellRun::new_at(
                        base.offset_by_bytes(first * element.byte_width()),
                        element.byte_width(),
                        element,
                        length,
                        run.source_point().clone(),
                        mode,
                        IndexIntervals::default(),
                    ));
                }
            }
            for (at, value) in self.cells.concrete_region_candidates(pointer, bytes) {
                crate::instrumentation::record_deterministic_work(1);
                let (cell_stem, cell_start) = offset_stem_and_constant(&at.offset);
                if cell_stem != stem {
                    continue;
                }
                let delta = cell_start
                    .checked_sub(start)
                    .ok_or(RuntimeError::TypeMismatch)?;
                if delta + i64::from(value.byte_width()) <= 0 || delta >= i64::from(bytes) {
                    continue;
                }
                if delta < 0
                    || delta + width > i64::from(bytes)
                    || delta % width != 0
                    || value.program_type() != element
                {
                    return Err(RuntimeError::TypeMismatch);
                }
                let index = (delta / width) as u32;
                represented.insert(index);
                captured_cells.push((
                    base.offset_by_bytes(index * element.byte_width()),
                    value.clone(),
                ));
            }
            if represented != IndexIntervals::full(count) {
                let source = copy_source
                    .filter(|point| point.has_certified_read_view())
                    .cloned()
                    .unwrap_or_else(|| ProgramPoint::of_memory(&self));
                captured_runs.push(CellRun::new_at(
                    base.clone(),
                    element.byte_width(),
                    element,
                    count,
                    source,
                    RunValueMode::Copy {
                        source_base: pointer.clone(),
                    },
                    represented,
                ));
            }
        } else {
            if value.program_type() != element {
                return Err(RuntimeError::TypeMismatch);
            }
            captured_runs.push(CellRun::new_with_mode(
                base.clone(),
                element.byte_width(),
                element,
                count,
                crate::kernel::intern_memory(SymbolicMemory::new()),
                RunValueMode::Constant(value),
                IndexIntervals::default(),
            ));
        }
        if !fresh {
            self = self.without_possible_aliasing_cells(base, bytes, assumptions);
        }
        for run in captured_runs {
            let derivation_base = intern_derivation_base(&mut self);
            std::sync::Arc::make_mut(&mut self.cells).add_run(run.clone());
            record_memory_derivation(
                &mut self,
                MemoryDerivation::CellsSeeded {
                    base: derivation_base,
                    run: std::sync::Arc::new(run),
                },
            );
        }
        for (at, value) in captured_cells {
            self = self.store_with_context(at, value, assumptions);
        }
        Ok(self.with_initialized_object(base, bytes))
    }

    /// Whether a run at `base` stands for the cells it seeds with nothing
    /// else to do: no typed union view to displace, and no live allocation
    /// the base may lie in to mark initialized.
    fn run_can_stand_for_cells_at(&self, base: &Address) -> bool {
        let candidates = AliasCandidates::of_block(&base.base);
        !candidates.any_entry(&self.heap.uninitialized_objects, |_, _| true)
            && !candidates.any_entry(&self.union_cells, |_, _| true)
            && !candidates.any_entry(&self.heap.live_allocations, |_, _| true)
    }

    /// The run of [`Self::with_seeded_cells_at`], its preconditions checked.
    fn with_run_of_cells(
        mut self,
        base: Address,
        element_width: u32,
        element_type: ProgramType,
        first: u32,
        count: u32,
        source: ProgramPoint,
        mode: RunValueMode,
    ) -> Self {
        let mut holes = IndexIntervals::default();
        holes.insert_range(0, first);
        let probe = CellRun::new_at(
            base.clone(),
            element_width,
            element_type,
            count,
            source,
            mode,
            IndexIntervals::default(),
        );
        // An element that already holds a cell keeps it: seeding skips it,
        // so it is a hole of the new run from the start. Only the cells of
        // the run's own block can be one of its slots.
        let own = AliasCandidates::only_block(&base.base);
        for (pointer, _) in own.entries(self.cells.concrete()) {
            if let Some(index) = probe.slot_index(pointer) {
                holes.insert(index);
            }
        }
        // A slot can match only on its exact address line. Reuse the cover
        // index before examining slots: unrelated parameter stems share the
        // external-argument block, but none of their elements can match.
        for run in self.cells.runs_meeting_slot_span(&probe) {
            crate::instrumentation::record_deterministic_work(1);
            if run.base() == &base && run.element_width() == element_width {
                // One spelling, one stride: the live slots of the older run
                // are the elements it has in common with this one.
                for (low, high) in run.holes().gaps(run.count()) {
                    holes.insert_range(low.min(count), high.min(count));
                }
                continue;
            }
            for index in run.live_indexes() {
                crate::instrumentation::record_deterministic_work(1);
                if let Some(slot) = probe.slot_index(&run.slot_pointer(index)) {
                    holes.insert(slot);
                }
            }
        }
        if holes.count() >= u64::from(count) {
            return self;
        }
        let run = probe.with_holes(holes);
        let derivation_base = intern_derivation_base(&mut self);
        std::sync::Arc::make_mut(&mut self.cells).add_run(run.clone());
        record_memory_derivation(
            &mut self,
            MemoryDerivation::CellsSeeded {
                base: derivation_base,
                run: std::sync::Arc::new(run),
            },
        );
        self
    }

    pub fn store(self, pointer: Address, value: ProgramValue) -> Self {
        self.store_with_context(pointer, value, &PureFactContext::new())
    }

    /// Observe and cache a scalar cell without changing its physical bytes.
    /// The observation is computed here so callers cannot supply a new value
    /// under the guise of a read.
    #[cfg(test)]
    pub(crate) fn materialize_symbolic_cell(
        self,
        pointer: Address,
        program_type: ProgramType,
    ) -> Self {
        let value = crate::kernel::eval::symbolic_storage_cell_value(
            &self,
            None,
            &pointer,
            program_type,
            true,
        );
        match value {
            Some(value) => self.materialize_named_cell(pointer, value),
            None => self,
        }
    }

    /// Name one contract field at its selected source state without
    /// recording a program write. The producer's source is shared by all
    /// fields of the same entry object; deriving the value here preserves
    /// that identity without accepting an arbitrary cached value.
    pub(crate) fn materialize_cell_from_source(
        self,
        pointer: Address,
        program_type: ProgramType,
        source: SharedMemory,
    ) -> Self {
        self.materialize_cell_at(pointer, program_type, &ProgramPoint::unplaced(&source))
    }

    pub(crate) fn materialize_cell_at(
        self,
        pointer: Address,
        program_type: ProgramType,
        source: &ProgramPoint,
    ) -> Self {
        let value = crate::kernel::eval::canonical_cell_value(source, &pointer, program_type);
        self.materialize_named_cell(pointer, value)
    }

    pub(crate) fn materialize_entry_integer_cell_at(
        self,
        pointer: Address,
        source: &ProgramPoint,
    ) -> Self {
        let Some(read) = crate::kernel::eval::observe_entry_integer_cell(source, &pointer) else {
            return self;
        };
        self.materialize_named_cell(pointer, ProgramValue::Int32(read))
    }

    /// Cache the canonical value of an already existing cell for a resource
    /// projection. This is not a C write and cannot establish initialization.
    /// Kernel producers supply the value they observed or proved at this point.
    pub(in crate::kernel) fn materialize_named_cell(
        mut self,
        pointer: Address,
        value: ProgramValue,
    ) -> Self {
        if self.cells.contains_key(&pointer) {
            return self;
        }
        if self.may_read_uninitialized_object(&pointer, value.byte_width())
            && !self.has_initialized_bytes_at(&pointer, value.byte_width())
        {
            return self;
        }
        // A logical name does not initialize an automatic object either.
        // A real local store has already materialized its cell above.
        if pointer.base.is_local_block() && self.has_block(&pointer.base) {
            return self;
        }
        // A named load must not turn fresh malloc storage into a value.  The
        // exact typed-cell mark is the authority that a prior C store
        // initialized this address; the lookup is local to its heap block.
        if matches!(pointer.base, AddressBase::Heap(_)) {
            let base = pointer.with_offset(AddressOffset::constant(0));
            if (self.heap.uninitialized_allocations.contains(&base)
                || self.heap.zeroed_allocations.contains(&base)
                || self.heap.zeroed_prefix_allocations.contains_key(&base))
                && !self.has_initialized_bytes_at(&pointer, value.byte_width())
            {
                return self;
            }
        }
        let base = intern_derivation_base(&mut self);
        std::sync::Arc::make_mut(&mut self.cells).insert(pointer, value);
        record_memory_derivation(&mut self, MemoryDerivation::CellObserved { base });
        self
    }

    /// Writes one cell. The transition's fact context is not recorded on the
    /// store edge: a later load of another cell of the same base crosses the
    /// edge only with distinctness evidence checked in the querying context.
    pub fn store_with_context(
        self,
        pointer: Address,
        value: ProgramValue,
        context: &PureFactContext,
    ) -> Self {
        self.store_with_effective_type(pointer, value.into(), context, None, false, None)
    }

    /// [`Self::store_with_context`] for a C store through an lvalue of
    /// `class`, which also records the effective type it gives a heap cell
    /// (`design/effective-types.md`). Like the initialized bytes, the record
    /// changes with the cell under the one store edge, so the memory history
    /// stays connected.
    #[cfg(test)]
    pub(in crate::kernel) fn store_classed_with_context(
        self,
        pointer: Address,
        value: ProgramValue,
        context: &PureFactContext,
        class: Option<crate::kernel::effective_type::CAccessClass>,
    ) -> Self {
        self.store_with_effective_type(pointer, value.into(), context, Some(class), true, None)
    }

    /// Apply a program store and its cache invalidation as one transition.
    pub(in crate::kernel) fn store_invalidating_with_context(
        self,
        pointer: Address,
        value: ProgramValue,
        context: &PureFactContext,
    ) -> Self {
        self.store_with_effective_type(pointer, value.into(), context, None, true, None)
    }

    pub(in crate::kernel) fn store_retained(self, pointer: Address, value: ExecutionValue) -> Self {
        self.store_with_effective_type(
            pointer,
            value.into(),
            &PureFactContext::new(),
            None,
            false,
            None,
        )
    }

    pub(in crate::kernel) fn store_retained_with_context(
        self,
        pointer: Address,
        value: ExecutionValue,
        context: &PureFactContext,
    ) -> Self {
        self.store_with_effective_type(pointer, value.into(), context, None, false, None)
    }

    pub(in crate::kernel) fn store_retained_classed_with_context(
        self,
        pointer: Address,
        value: ExecutionValue,
        context: &PureFactContext,
        class: Option<crate::kernel::effective_type::CAccessClass>,
        authorized_range: Option<&MemoryRange>,
    ) -> Self {
        self.store_with_effective_type(
            pointer,
            value.into(),
            context,
            Some(class),
            true,
            authorized_range,
        )
    }

    fn store_with_effective_type(
        mut self,
        pointer: Address,
        value: StoredMemoryValue,
        context: &PureFactContext,
        effective_type: Option<Option<crate::kernel::effective_type::CAccessClass>>,
        invalidate_aliases: bool,
        authorized_range: Option<&MemoryRange>,
    ) -> Self {
        crate::kernel::debug_assert_widths(
            "a stored value",
            || crate::kernel::value_mismatch(value.native()),
            value.value(),
        );
        let base = intern_derivation_base(&mut self);
        // Cache invalidation is internal to this store, not a memory event.
        // Retain its original input, and never intern the intermediate cache.
        if (invalidate_aliases
            || !self.union_cells.is_empty()
            || !self.heap.initialized.partial_map().is_empty())
            && let Some((mut prepared, lost_knowledge)) = self.prepare_store_cache_of(
                &pointer,
                value.byte_width(),
                crate::kernel::assumptions::access_extent_of_type(
                    value.program_type(),
                    value.byte_width(),
                ),
                context,
                authorized_range,
            )
        {
            if lost_knowledge {
                prepared.mark_forgotten_from(&base);
            }
            self = prepared;
        }
        std::sync::Arc::make_mut(&mut self.cells).insert_retained(pointer.clone(), value.clone());
        if !self.heap.initialized.partial_map().is_empty() {
            Arc::make_mut(&mut self.heap)
                .initialized
                .forget_masks(&pointer, value.byte_width());
        }
        if (self.is_live_heap_address(&pointer, context)
            || !self.heap.uninitialized_objects.is_empty())
            && !self.heap.initialized.covers(&pointer, value.byte_width())
        {
            std::sync::Arc::make_mut(&mut self.heap)
                .initialized
                .record(&pointer, value.byte_width());
        }
        if let Some(class) = effective_type
            && matches!(pointer.base, AddressBase::Heap(_))
        {
            let mut record = self.heap.effective_types.clone();
            if record.record(&pointer, value.byte_width(), class, value.native()) {
                std::sync::Arc::make_mut(&mut self.heap).effective_types = record;
            }
        }
        // Skipped when empty so an ordinary store neither visits nor
        // reallocates the shared overlay map.
        if !self.union_cells.is_empty() {
            self.remove_union_views_at(&pointer);
        }
        record_memory_derivation(
            &mut self,
            MemoryDerivation::Store {
                base,
                pointer,
                value,
            },
        );
        self
    }

    pub fn load(&self, pointer: &Address) -> ExpressionOutcome {
        match self.cells.get(pointer) {
            Some(value) => ExpressionOutcome::Value(value),
            None => ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory),
        }
    }

    /// The pointers at which the two states' cells or typed union views
    /// differ, ascending. A pointer differs exactly when some entry keyed by
    /// it is in one map's diff, so this walks only the paths the states
    /// do not share.
    pub fn differing_cell_pointers(&self, other: &Self) -> Vec<Address> {
        let mut pointers = self
            .cells
            .differing_pointers(&other.cells)
            .into_iter()
            .collect::<BTreeSet<_>>();
        #[cfg(debug_assertions)]
        if self
            .cells
            .runs()
            .chain(other.cells.runs())
            .all(|run| run.count() <= crate::kernel::primitives::CHECKED_RUN_SLOTS)
        {
            crate::instrumentation::uncharged_debug_check(|| {
                let expected = self
                    .cells
                    .diff(&other.cells)
                    .map(|change| change.key().clone())
                    .collect::<BTreeSet<_>>();
                assert_eq!(
                    pointers, expected,
                    "the runs' differing slots disagree with the logical diff"
                );
            });
        }
        pointers.extend(
            self.union_cells
                .diff(&other.union_cells)
                .map(|change| change.key().0.clone()),
        );
        pointers.into_iter().collect()
    }

    /// [`Self::differing_cell_pointers`] for a caller asking about a load of
    /// `bytes` bytes at `pointer`: a run's differing slots that the load's
    /// bytes provably miss by their constant distance from it are left out.
    /// Those cells cannot change what the load reads, which is all the
    /// callers ask of each differing cell.
    pub(in crate::kernel) fn differing_cell_pointers_meeting_load(
        &self,
        other: &Self,
        pointer: &Address,
        bytes: u32,
    ) -> Vec<Address> {
        let differing = self.cells.differing_cells(&other.cells);
        let mut pointers = differing.pointers.into_iter().collect::<BTreeSet<_>>();
        for (run, slots) in differing.run_slots {
            crate::instrumentation::record_deterministic_work(1);
            match crate::kernel::reasoning::memory_resolution::run_access(&run, pointer) {
                crate::kernel::reasoning::memory_resolution::RunAccess::DistinctBlock => {}
                crate::kernel::reasoning::memory_resolution::RunAccess::Shift(shift) => {
                    let (low, high) =
                        crate::kernel::reasoning::memory_resolution::run_elements_meeting(
                            &run,
                            shift,
                            i64::from(bytes.max(1)),
                        );
                    for index in low..high {
                        crate::instrumentation::record_deterministic_work(1);
                        if slots.contains(index) {
                            pointers.insert(run.slot_pointer(index));
                        }
                    }
                }
                _ => {
                    crate::instrumentation::record_deterministic_work(
                        usize::try_from(slots.count()).unwrap_or(usize::MAX),
                    );
                    pointers.extend(slots.indexes().map(|index| run.slot_pointer(index)));
                }
            }
        }
        pointers.extend(
            self.union_cells
                .diff(&other.union_cells)
                .map(|change| change.key().0.clone()),
        );
        pointers.into_iter().collect()
    }

    pub(in crate::kernel) fn known_retained_value(
        &self,
        pointer: &Address,
    ) -> Option<ExecutionValue> {
        self.cells.get_retained(pointer)
    }

    pub(in crate::kernel) fn known_value(&self, pointer: &Address) -> Option<ProgramValue> {
        self.cells.get(pointer)
    }

    /// Borrow an explicit cell without deriving a value for an array run slot.
    pub(in crate::kernel) fn indexed_scalar_value(
        &self,
        pointer: &Address,
    ) -> Option<&ProgramValue> {
        self.cells.explicitly_stored_value(pointer)
    }

    /// Borrow an exact cell value, including the payload of a constant run.
    pub(in crate::kernel) fn indexed_stored_value(
        &self,
        pointer: &Address,
    ) -> Option<&ProgramValue> {
        self.cells.exact_stored_value(pointer)
    }

    /// Check the exact typed cell or a fully initialized declared word
    /// without evaluating a load, resolving aliases, or walking history.
    pub(in crate::kernel) fn indexed_read_is_defined(
        &self,
        pointer: &Address,
        value_type: ProgramType,
    ) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        if !self.heap.deallocated_allocations.is_empty()
            || self.heap.uninitialized_allocations.len() != 0
            || !self.heap.zeroed_prefix_allocations.is_empty()
            || self.is_ended_local_address(pointer)
        {
            return false;
        }
        if let Some(value) = self.indexed_scalar_value(pointer) {
            return value_type.accepts(value) || value_type.read_cell(value).is_some();
        }
        match self.cells.exact_run_slot_type(pointer) {
            Ok(Some(stored_type)) => stored_type == value_type,
            Err(()) => false,
            // The whole representation of a declared uint32 is valid once
            // all its bytes are initialized, including after character writes.
            Ok(None) => {
                value_type == ProgramType::UInt32
                    && self.is_live_declared_local_uint32(pointer)
                    && self.has_initialized_bytes_at(pointer, value_type.byte_width())
            }
        }
    }

    pub(in crate::kernel) fn is_live_declared_local_uint32(&self, pointer: &Address) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        pointer.base.is_local_block()
            && matches!(pointer.offset.view(), OffsetView::Constant(0))
            && !self.is_ended_local_address(pointer)
            && self.blocks.get(&pointer.base).is_some_and(|block| {
                block.declared_scalar_type == Some(ProgramType::UInt32)
                    && block.size().as_const() == Some(ProgramType::UInt32.byte_width())
            })
    }

    /// The integer terms held by the concrete cells this memory changed
    /// since `earlier`, or by every concrete cell when there is no earlier
    /// memory: what a recorded point newly names in memory. The walk visits
    /// only the changed cells of memories derived from one another.
    pub(crate) fn changed_cell_integers<'a>(
        &'a self,
        earlier: Option<&'a Self>,
    ) -> Vec<&'a OldMachineTerm> {
        self.cells
            .changed_concrete_cells(earlier.map(|earlier| earlier.cells.as_ref()))
            .into_iter()
            .filter_map(|(_, value)| match value.numeric_value() {
                ProgramValue::Bool(term)
                | ProgramValue::Int8(term)
                | ProgramValue::Int16(term)
                | ProgramValue::Int32(term)
                | ProgramValue::UInt8(term)
                | ProgramValue::UInt16(term)
                | ProgramValue::UInt32(term)
                | ProgramValue::Int64(term)
                | ProgramValue::UInt64(term)
                | ProgramValue::Int128(term)
                | ProgramValue::UInt128(term) => Some(term),
                _ => None,
            })
            .collect()
    }

    pub(in crate::kernel) fn has_known_cell_at(&self, pointer: &Address) -> bool {
        self.cells.contains_key(pointer) || self.has_union_overlay_at(pointer)
    }

    pub(in crate::kernel) fn join_cell_width(&self, pointer: &Address) -> u32 {
        self.union_views_at(pointer)
            .map(|((_, ty), _)| {
                crate::instrumentation::record_deterministic_work(1);
                ty.byte_width()
            })
            .chain(self.cells.get(pointer).map(|value| value.byte_width()))
            .max()
            .unwrap_or(0)
    }

    /// The typed union views recorded at exactly `pointer`: one key range,
    /// since `(Pointer, ProgramType)` keys order by pointer first.
    fn union_views_at<'a>(
        &'a self,
        pointer: &'a Address,
    ) -> impl Iterator<Item = (&'a (Address, ProgramType), &'a ProgramValue)> + 'a {
        self.union_cells
            .range::<_, (Address, ProgramType)>((pointer.clone(), ProgramType::Void)..)
            .take_while(move |((cell_pointer, _), _)| cell_pointer == pointer)
            .map(|(key, value)| (key, value.native()))
    }

    /// Drops every typed union view at exactly `pointer`.
    fn remove_union_views_at(&mut self, pointer: &Address) {
        let views = self
            .union_views_at(pointer)
            .map(|(key, _)| key.clone())
            .collect::<Vec<_>>();
        if views.is_empty() {
            return;
        }
        let union_cells = std::sync::Arc::make_mut(&mut self.union_cells);
        for view in views {
            union_cells.remove(&view);
        }
    }

    /// Whether the `byte_width` bytes at `pointer` are recorded initialized,
    /// whether or not a cached value for them survives (see
    /// [`InitializedBytes`]). A constant offset is covered by the run of its
    /// block holding it; a symbolic offset by the same spelling.
    pub(in crate::kernel) fn has_initialized_bytes_at(
        &self,
        pointer: &Address,
        byte_width: u32,
    ) -> bool {
        self.heap.initialized.covers(pointer, byte_width)
    }

    /// Whether every byte of `block` in `start..end` was written: held by a
    /// run of the initialization record or by a cached constant-offset cell.
    /// A cell is evidence its bytes were written, as the record is for the
    /// bytes whose cached values were forgotten, so a byte either holds is
    /// initialized. Walks the bytes left to right, one predecessor lookup in
    /// each map per run or cell crossed: the work is the entries inside the
    /// interval, not the block or the memory.
    fn written_interval(&self, block: &AddressBase, start: i64, end: i64) -> bool {
        let at = |offset: i64| Address::new(block.clone(), AddressOffset::constant(offset));
        let concrete = self.cells.concrete();
        let mut cursor = start;
        while cursor < end {
            if let Some(run_end) = self.heap.initialized.run_end_holding(block, cursor) {
                cursor = run_end;
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            let cell_end = concrete
                .range(at(i64::MIN)..=at(cursor))
                .next_back()
                .and_then(|(cell, value)| {
                    Some(cell.offset.as_const()? + i64::from(value.byte_width()))
                })
                .filter(|cell_end| *cell_end > cursor);
            match cell_end {
                Some(cell_end) => cursor = cell_end,
                None => return false,
            }
        }
        true
    }

    /// Whether the `byte_width` bytes at `pointer` were written, by the
    /// initialization record or a cached cell (see [`Self::written_interval`]),
    /// also for an element index the facts bound: `a[u]` under `0 <= u < n`
    /// reads bytes of `a[0..n]`, so a run or cells covering all of those
    /// cover the read wherever `u` lands. The bound is the index's signed
    /// interval; the offset must be the block's base plus one scaled index
    /// and a constant, as an element access is.
    pub(in crate::kernel) fn has_initialized_bytes_under(
        &self,
        pointer: &Address,
        byte_width: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        if self.has_initialized_bytes_at_spelling_under(pointer, byte_width, assumptions) {
            return true;
        }
        // Constructor storage retains its identity under argument aliases.
        // Query only this pointer's indexed equality class, never all facts.
        !self.heap.uninitialized_objects.is_empty()
            && assumptions
                .equality_graph
                .pointer_spellings(pointer)
                .iter()
                .any(|alias| {
                    crate::instrumentation::record_deterministic_work(1);
                    self.has_initialized_bytes_at_spelling_under(alias, byte_width, assumptions)
                })
    }

    fn has_initialized_bytes_at_spelling_under(
        &self,
        pointer: &Address,
        byte_width: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        if self.has_initialized_bytes_at(pointer, byte_width) {
            return true;
        }
        if let Some(offset) = pointer.offset.as_const() {
            return self.written_interval(&pointer.base, offset, offset + i64::from(byte_width));
        }
        let (atoms, shift) =
            crate::kernel::reasoning::memory_resolution::offset_atoms_and_constant(&pointer.offset);
        let [atom] = atoms.as_slice() else {
            return false;
        };
        let OffsetView::Int32Scaled {
            index: value,
            byte_width: scale,
        } = atom.view()
        else {
            return false;
        };
        if scale <= 0 {
            return false;
        }
        let interval = match value.operand_view().read_source() {
            Some(leaf) => assumptions.signed_interval(&leaf),
            None => assumptions.signed_interval_view(value.operand_view()),
        };
        let Some((low, high)) = interval else {
            return false;
        };
        let (Some(start), Some(end)) = (
            low.checked_mul(scale)
                .and_then(|bytes| bytes.checked_add(shift)),
            high.checked_mul(scale)
                .and_then(|bytes| bytes.checked_add(shift))
                .and_then(|bytes| bytes.checked_add(i64::from(byte_width))),
        ) else {
            return false;
        };
        start < end && self.written_interval(&pointer.base, start, end)
    }

    /// Whether any typed union overlay is recorded at exactly this pointer.
    ///
    /// A union overlay is the authoritative view for an exact typed load, so a
    /// reader that wants to treat the raw cell as the pointer's content has to
    /// know that no overlay outranks it. [`Self::store_with_context`] and
    /// [`Self::store_union_views`] keep the two disjoint at every pointer, so
    /// this answers `false` wherever [`Self::known_value`] answers `Some`; it is
    /// asked anyway where the consequence of the two ever coexisting would be
    /// a wrong value rather than a lost one.
    pub(in crate::kernel) fn has_union_overlay_at(&self, pointer: &Address) -> bool {
        self.union_views_at(pointer).next().is_some()
    }

    pub(in crate::kernel) fn known_union_value(
        &self,
        pointer: &Address,
        value_type: ProgramType,
    ) -> Option<ProgramValue> {
        self.known_retained_union_value(pointer, value_type)
            .map(ExecutionValue::into_native)
    }

    /// Borrow the immutable view of one exact typed union cell.
    pub(in crate::kernel) fn indexed_union_value(
        &self,
        pointer: &Address,
        value_type: ProgramType,
    ) -> Option<&ProgramValue> {
        self.union_cells
            .get(&(pointer.clone(), value_type))
            .map(StoredMemoryValue::native)
    }

    pub(in crate::kernel) fn known_retained_union_value(
        &self,
        pointer: &Address,
        value_type: ProgramType,
    ) -> Option<ExecutionValue> {
        self.union_cells
            .get(&(pointer.clone(), value_type))
            .map(|value| value.value().clone())
    }

    /// The pointer a typed union view records at exactly `pointer`, when one
    /// does: one key range, as [`Self::union_views_at`] reads it.
    pub(in crate::kernel) fn known_union_pointer(&self, pointer: &Address) -> Option<ProgramValue> {
        self.union_views_at(pointer)
            .find(|(_, value)| matches!(value, ProgramValue::Pointer(_)))
            .map(|(_, value)| value.clone())
    }

    #[cfg(test)]
    pub(in crate::kernel) fn store_union(
        self,
        pointer: Address,
        value_type: ProgramType,
        value: ProgramValue,
    ) -> Self {
        self.store_union_views(
            pointer.clone(),
            value_type.byte_width(),
            vec![(pointer, value_type, value)],
        )
    }

    /// Replaces the bytes in a union region, then records typed views that
    /// were all derived from that same byte image.
    ///
    /// A direct member write uses a one-view batch, invalidating old overlays
    /// that overlap its bytes. Aggregate initialization and copy use this
    /// batch form because their member views are read from one unchanged
    /// image rather than from sequential writes.
    pub(in crate::kernel) fn store_union_views(
        self,
        written_pointer: Address,
        written_bytes: u32,
        views: Vec<(Address, ProgramType, ProgramValue)>,
    ) -> Self {
        self.store_retained_union_views(
            written_pointer,
            written_bytes,
            views
                .into_iter()
                .map(|(pointer, ty, value)| (pointer, ty, value.into()))
                .collect(),
        )
    }

    pub(in crate::kernel) fn store_retained_union_views(
        self,
        written_pointer: Address,
        written_bytes: u32,
        views: Vec<(Address, ProgramType, ExecutionValue)>,
    ) -> Self {
        let diagnostic_base = self.clone();
        let mut memory = self.without_possible_aliasing_cells(
            &written_pointer,
            written_bytes,
            &PureFactContext::new(),
        );
        let mut initialized = Vec::new();
        for (pointer, value_type, value) in views {
            std::sync::Arc::make_mut(&mut memory.union_cells)
                .insert((pointer.clone(), value_type), value.into());
            if (memory.is_live_heap_address(&pointer, &PureFactContext::new())
                || !memory.heap.uninitialized_objects.is_empty())
                && !memory.has_initialized_bytes_at(&pointer, value_type.byte_width())
            {
                initialized.push((pointer, value_type.byte_width()));
            }
        }
        if !initialized.is_empty() {
            let record = &mut std::sync::Arc::make_mut(&mut memory.heap).initialized;
            for (pointer, width) in initialized {
                record.record(&pointer, width);
            }
        }
        memory.record_diagnostic_transform(
            "replace union views",
            vec![diagnostic_base],
            vec![
                ProgramValue::pointer(written_pointer.clone()),
                ProgramValue::Int32(written_bytes.into()),
            ],
        );
        memory
    }

    /// Drops every cell a field of `program_type` at `offset_bytes` from `base`
    /// could occupy.
    ///
    /// Used where a copy cannot carry a field's value: leaving the
    /// destination's own cells would read back as its previous contents,
    /// which no execution of the copy produces.
    pub(in crate::kernel) fn without_field_cells(
        &self,
        base: &Address,
        offset_bytes: u32,
        program_type: ProgramType,
    ) -> Self {
        let diagnostic_base = self.clone();
        let Some(field_start) = base
            .offset
            .as_const()
            .map(|start| start + i64::from(offset_bytes))
        else {
            return self.clone();
        };
        let field_end = field_start + i64::from(program_type.byte_width());
        let mut memory = self.clone();
        let source = intern_memory_ref(&memory);
        let overlaps = |pointer: &Address| {
            pointer.base == base.base
                && pointer
                    .offset
                    .as_const()
                    .is_some_and(|offset| offset >= field_start && offset < field_end)
        };
        // `overlaps` holds only in the base's own block.
        let own = AliasCandidates::only_block(&base.base);
        memory.forget_cached_values(
            ForgetScope::candidates(&own),
            |pointer, _| {
                if overlaps(pointer) {
                    CachedValueFate::Forgotten
                } else {
                    CachedValueFate::Kept
                }
            },
            ask_every_slot,
        );
        // The field's bytes now hold something the copy cannot name, whether
        // or not a value was cached for them, so no zero reading answers for
        // them either.
        memory.forget_zero_readings_under(std::iter::once(&base.base));
        // The copy wrote the field with no value it can name, from a source
        // whose field it could not check, so its bytes are not known
        // initialized either.
        memory.forget_initialized_bytes(
            &base.with_offset(AddressOffset::constant(field_start)),
            program_type.byte_width(),
        );
        // Nothing restores these cells — the copy could not carry the field —
        // so the result knows strictly less than its source and must not be
        // able to re-intern as a state that never knew it. See
        // [`SymbolicMemory::mark_forgotten_from`].
        if memory.cells.len() != self.cells.len()
            || memory.union_cells.len() != self.union_cells.len()
        {
            memory.mark_forgotten_from(&source);
        }
        memory.record_diagnostic_transform(
            "forget copied field contents",
            vec![diagnostic_base],
            vec![
                ProgramValue::pointer(base.clone()),
                ProgramValue::Int32(offset_bytes.into()),
                ProgramValue::Int32(program_type.byte_width().into()),
            ],
        );
        memory
    }

    pub(in crate::kernel) fn without_cell(&self, pointer: &Address) -> Self {
        let diagnostic_base = self.clone();
        let mut memory = self.clone();
        std::sync::Arc::make_mut(&mut memory.cells).remove(pointer);
        memory.remove_union_views_at(pointer);
        // The hypothetical memory a load's distinct case reads also drops the
        // cell's initialization mark, as it always has, so it re-interns as
        // the state before the store that wrote the cell when nothing else
        // differs. Only that load reads it, at an address distinct from the
        // cell's.
        let width = self
            .cells
            .get(pointer)
            .map_or(0, |value| value.byte_width());
        memory.forget_initialized_bytes(pointer, width);
        memory.record_diagnostic_transform(
            "remove cell for conditional load",
            vec![diagnostic_base],
            vec![ProgramValue::pointer(pointer.clone())],
        );
        memory
    }

    /// Records the bytes of cells whose cached values an operation dropped
    /// as initialized wherever a later read must establish initialization.
    /// Automatic storage always needs that record. An unwritten-object marker
    /// also makes external reads check it: their input observations may predate
    /// the marker, so losing a cached value must retain those initialized bytes.
    /// Heap stores already record their bytes. Costs only the dropped cells.
    fn record_dropped_initialized_cells(&mut self, dropped: &[(Address, u32)]) {
        let mut record = self.heap.initialized.clone();
        let mut changed = false;
        for (pointer, width) in dropped {
            if pointer.base.is_local_block()
                || pointer.base == AddressBase::ExternalArgument
                || !self.heap.uninitialized_objects.is_empty()
            {
                changed |= record.record(pointer, *width);
            }
        }
        if changed {
            std::sync::Arc::make_mut(&mut self.heap).initialized = record;
        }
    }

    /// The one way a memory transition drops cached contents.
    ///
    /// A state records what an address holds in more than one place: a
    /// cell (or one slot of a run), a typed union view keyed by the member
    /// type it records, and, for `calloc` storage, the zero reading that
    /// answers for every byte no cached value covers. Each of them is an
    /// authoritative answer to some load, so a transition that forgets bytes
    /// has to forget every one of them, or the survivor answers for bytes the
    /// transition no longer knows. Loop havoc used to drop cells alone: a
    /// union view written inside the loop survived it, and so did the zero
    /// reading of an allocation the loop wrote, and both read back the
    /// pre-loop value (`mdtests/a_loop_that_writes_a_union_member_forgets_its_view.md`,
    /// `mdtests/a_loop_that_writes_calloc_storage_forgets_its_zero_reading.md`).
    ///
    /// So every forgetting transition goes through here. `fate` decides each
    /// cell and each union view by the same rule; `run_rule` answers for a
    /// run as a whole, as [`CellStore::retain_candidates_outside_by`] asks.
    /// What is [`CachedValueFate::Forgotten`] then also loses its zero
    /// reading, and stays recorded initialized wherever later reads require
    /// initialization evidence (a write only ever initializes). A new
    /// representation of cached bytes belongs in this function, so no
    /// transition can miss it.
    ///
    /// The slots `run_rule` drops as a whole run are recorded initialized
    /// where later reads require evidence ([`Self::record_dropped_initialized_run_slots`]),
    /// whatever `fate` would say of them: a dropped slot was written, and a
    /// caller that retires the storage forgets its record afterwards. A run
    /// carries no zero reading to lose: it is never seeded where a live
    /// allocation may lie ([`Self::with_seeded_cells_at`] and its siblings
    /// refuse one).
    ///
    /// The work is the candidates `scope` admits, which every caller already
    /// pays for its cells; the union views are asked only when the state
    /// holds some, and the zero readings only when it holds some. Returns
    /// whether any value was [`CachedValueFate::Forgotten`].
    pub(super) fn forget_cached_values(
        &mut self,
        scope: ForgetScope<'_>,
        mut fate: impl FnMut(&Address, CachedValue<'_>) -> CachedValueFate,
        run_rule: impl FnMut(&CellRun) -> (SlotSet, crate::kernel::primitives::RuleAnswer),
    ) -> bool {
        let mut forgotten_cells = Vec::new();
        let dropped_run_slots;
        {
            let mut keep_cell = |pointer: &Address, value: &ProgramValue| match fate(
                pointer,
                CachedValue::Cell(value),
            ) {
                CachedValueFate::Kept => true,
                CachedValueFate::Overwritten | CachedValueFate::Retired => false,
                CachedValueFate::Forgotten => {
                    push_dropped_initialized(
                        &mut forgotten_cells,
                        (pointer.clone(), value.byte_width()),
                    );
                    false
                }
            };
            let cells = std::sync::Arc::make_mut(&mut self.cells);
            dropped_run_slots = match scope {
                ForgetScope::Everywhere => cells.retain_by(&mut keep_cell, run_rule),
                ForgetScope::Ordered {
                    candidates,
                    selected,
                    runs,
                    ..
                } => cells.retain_selected_concrete_by(
                    selected,
                    candidates,
                    runs,
                    &mut keep_cell,
                    run_rule,
                ),
                ForgetScope::Candidates {
                    candidates,
                    cells_kept,
                } => cells.retain_candidates_outside_by(
                    candidates,
                    cells_kept,
                    &mut keep_cell,
                    run_rule,
                ),
            };
        }
        if !self.union_cells.is_empty() {
            let mut keep_view =
                |(pointer, program_type): &(Address, ProgramType),
                 value: &crate::kernel::StoredMemoryValue| match fate(
                    pointer,
                    CachedValue::UnionView(*program_type, value.native()),
                ) {
                    CachedValueFate::Kept => true,
                    CachedValueFate::Overwritten | CachedValueFate::Retired => false,
                    CachedValueFate::Forgotten => {
                        push_dropped_initialized(
                            &mut forgotten_cells,
                            (pointer.clone(), program_type.byte_width()),
                        );
                        false
                    }
                };
            let union_cells = std::sync::Arc::make_mut(&mut self.union_cells);
            match scope {
                ForgetScope::Everywhere => union_cells.retain(&mut keep_view),
                // A union view is never skipped by `cells_kept`: those ranges
                // are what the caller showed its *cell* rule keeps, and a
                // view is asked by its own width.
                ForgetScope::Candidates { candidates, .. }
                | ForgetScope::Ordered { candidates, .. } => {
                    candidates.retain_map(union_cells, &mut keep_view)
                }
            }
        }
        let forgot_partial = if self.heap.initialized.partial_map().is_empty() {
            false
        } else {
            let candidates = match scope {
                ForgetScope::Everywhere => None,
                ForgetScope::Candidates {
                    candidates,
                    cells_kept,
                }
                | ForgetScope::Ordered {
                    candidates,
                    cells_kept,
                    ..
                } => Some((candidates, cells_kept)),
            };
            Arc::make_mut(&mut self.heap)
                .initialized
                .forget_partial_values(candidates, |address, value| {
                    fate(address, CachedValue::Cell(value)) == CachedValueFate::Kept
                })
        };
        self.record_dropped_initialized_cells(&forgotten_cells);
        // A run's slots are cells too, dropped by `run_rule` as a whole run
        // without `fate` being asked; preserve their initialization evidence.
        self.record_dropped_initialized_run_slots(&dropped_run_slots);
        self.forget_zero_readings_under(forgotten_cells.iter().map(|(pointer, _)| &pointer.base));
        !forgotten_cells.is_empty() || forgot_partial
    }

    /// Drops the zero reading of every allocation that may hold a byte of
    /// `blocks`: every one in a block not proven distinct from one of them.
    /// A zero reading answers for the bytes no cached value covers, so once a
    /// cached value under it is forgotten, the reading would answer zero for
    /// bytes that held something else. The allocation goes as a whole, as a
    /// call's write set takes it ([`Self::forget_zeroed_allocations_written_by`]).
    /// Costs nothing when no allocation reads as zero, and otherwise the
    /// distinct blocks plus the readings dropped.
    fn forget_zero_readings_under<'a>(&mut self, blocks: impl Iterator<Item = &'a AddressBase>) {
        if self.heap.zeroed_allocations.len() == 0 && self.heap.zeroed_prefix_allocations.is_empty()
        {
            return;
        }
        let blocks = blocks.collect::<BTreeSet<_>>();
        for block in blocks {
            let candidates = AliasCandidates::of_block(block);
            if !candidates.any_element(&self.heap.zeroed_allocations, |_| true)
                && !candidates.any_entry(&self.heap.zeroed_prefix_allocations, |_, _| true)
            {
                continue;
            }
            let heap = std::sync::Arc::make_mut(&mut self.heap);
            candidates.retain_set(&mut heap.zeroed_allocations, |_| false);
            candidates.retain_map(&mut heap.zeroed_prefix_allocations, |_, _| false);
        }
    }

    /// [`Self::record_dropped_initialized_cells`] for run slots dropped as a whole
    /// run. A dropped interval whose bytes the record already holds costs
    /// one covering query: the usual case, as a declaration's initializer,
    /// which is what makes a run of automatic storage, records its whole
    /// object ([`Self::with_initialized_object`]). Otherwise contiguous
    /// slots are one run of bytes, and only slots strided apart or at a
    /// symbolic offset are recorded one by one, each as a dropped cell.
    fn record_dropped_initialized_run_slots(&mut self, dropped: &[DroppedRunSlots]) {
        if dropped.is_empty() {
            return;
        }
        let mut record = self.heap.initialized.clone();
        let mut changed = false;
        for DroppedRunSlots { run, elements } in dropped {
            if !run.base().base.is_local_block() && self.heap.uninitialized_objects.is_empty() {
                continue;
            }
            let width = run.value_width();
            for (low, high) in elements.intervals() {
                if low >= high {
                    continue;
                }
                let first = run.slot_pointer(low);
                let span = first.offset.as_const().zip(
                    run.slot_pointer(high - 1)
                        .offset
                        .as_const()
                        .map(|last| last + i64::from(width)),
                );
                if let Some((start, end)) = span {
                    if record.covers_interval(&first.base, start, end) {
                        continue;
                    }
                    if run.element_width() == width
                        && let Ok(bytes) = u32::try_from(end - start)
                    {
                        changed |= record.record(&first, bytes);
                        continue;
                    }
                }
                for index in low..high {
                    changed |= record.record(&run.slot_pointer(index), width);
                }
            }
        }
        if changed {
            std::sync::Arc::make_mut(&mut self.heap).initialized = record;
        }
    }

    /// Records the `bytes` bytes of the object at `pointer` as initialized:
    /// a declaration whose initializer writes every byte of its object
    /// (C11 6.7.9p21 zero-initializes whatever it does not name), or one value
    /// field guaranteed initialized by a checked construction summary. The
    /// cells describe values; this record outlives forgetting those values.
    pub(in crate::kernel) fn with_initialized_object(self, pointer: &Address, bytes: u32) -> Self {
        self.record_object_initialization(pointer, bytes, None)
    }

    /// The checked call initialized a whole local, with an unknown value.
    /// Retain the effect even if an earlier call initialized the same bytes.
    pub(in crate::kernel) fn with_initialized_call_output(
        self,
        pointer: &Address,
        bytes: u32,
    ) -> Self {
        let kind = self
            .blocks
            .get(&pointer.base)
            .filter(|block| block.size().as_const() == Some(bytes))
            .and_then(|block| block.declared_scalar_type)
            .filter(|&ty| MachineIntegerType::from_program_type(ty).is_some())
            .and_then(LoadKind::of_type)
            .filter(|kind| {
                kind.byte_width() == bytes
                    && self.cells.explicitly_stored_value(pointer).is_none()
                    && self.cells.exact_run_slot_type(pointer) == Ok(None)
            });
        self.record_object_initialization(pointer, bytes, kind)
    }

    fn record_object_initialization(
        mut self,
        pointer: &Address,
        bytes: u32,
        call_output: Option<LoadKind>,
    ) -> Self {
        if call_output.is_some() || !self.heap.initialized.covers(pointer, bytes) {
            let base = intern_derivation_base(&mut self);
            std::sync::Arc::make_mut(&mut self.heap)
                .initialized
                .record(pointer, bytes);
            record_memory_derivation(
                &mut self,
                MemoryDerivation::ObjectInitializationRecorded {
                    base,
                    pointer: pointer.clone(),
                    bytes,
                    call_output,
                },
            );
        }
        self
    }

    /// Forgets the initialization of the `byte_width` bytes at `pointer`
    /// (see [`InitializedBytes::forget`]), leaving the heap shared when the
    /// record holds none of them.
    fn forget_initialized_bytes(&mut self, pointer: &Address, byte_width: u32) {
        let mut record = self.heap.initialized.clone();
        if record.forget(pointer, byte_width) {
            std::sync::Arc::make_mut(&mut self.heap).initialized = record;
        }
    }

    /// Populate the derived cell partition while establishing function inputs,
    /// so the first field store pays only for its own cached cells.
    pub(crate) fn prepare_parameter_store_partition(
        &self,
        resources: &ResourceContext,
        assumptions: &PureFactContext,
    ) {
        self.cells.warm_parameter_partition(resources, assumptions);
        crate::kernel::reasoning::prepare_memory_variable_index(self);
    }

    /// Forgets every cell of `self` the write of `bytes` bytes at `pointer`
    /// may invalidate.
    ///
    /// Two independent reasons a cell goes. It may be *the same location*
    /// under some assignment of the symbolic offsets, which the address
    /// separation ladder below decides. Or its bytes may be *partly* the
    /// written ones while its address stays a different address: a one-byte
    /// write at `p + 4` overwrites the upper half of an `int64` cell at `p`,
    /// and `p + 4` is separate from `p` by every address test there is. Only
    /// the second reads a width, and it reads both sides' exact widths, so
    /// the cells that survive a store are the ones whose bytes the store
    /// provably misses.
    ///
    /// Both questions are asked of every cell. `overwrites` answers only
    /// where the two offsets carry the same symbolic atoms — it is the
    /// constant-gap test, and it declines a cell at `a[i]` against a store at
    /// `a[j]` — so the separation ladder below it was, on its own, deciding
    /// the byte question for exactly the pairs `overwrites` could not. It
    /// decided it from the addresses: `i != j` separates `a[i]` from `a[j]`
    /// and says nothing about an eight-byte store there, which covers
    /// `a[j]` and `a[j + 1]` both. So the ladder is conjoined with the shared
    /// [`crate::kernel::reasoning::access_byte_overlap`], exactly as
    /// `step_effect::cell_effect` and the state comparisons conjoin it: the
    /// ladder decides whether the addresses differ, and the byte answer
    /// decides whether the gap it establishes clears both accesses. An
    /// unknown gap blocks it too — a ladder proving two addresses differ says
    /// nothing about bytes.
    ///
    /// The widths are exact on both sides here, which is why this site can
    /// ask at all: the store's is its own `bytes`, and the cell's is the
    /// width of the value it holds, standing in the widest scalar where it
    /// holds none. Over-stating a width can only shrink the separated set,
    /// and a cell that stops being shown separate is dropped, which loses
    /// knowledge rather than keeping a stale value.
    pub(in crate::kernel) fn without_possible_aliasing_cells(
        &self,
        pointer: &Address,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> Self {
        let mut source = self.clone();
        let base = intern_derivation_base(&mut source);
        let Some((mut memory, lost_knowledge)) =
            source.prepare_store_cache(pointer, bytes, assumptions, None)
        else {
            return source;
        };
        if lost_knowledge {
            memory.mark_forgotten_from(&base);
        }
        let base_id = base.arena_id();
        record_memory_derivation(&mut memory, MemoryDerivation::CellsForgotten { base });
        debug_assert!(
            !lost_knowledge || intern_memory_ref(&memory).arena_id() > base_id,
            "a forget that lost knowledge landed on an older state"
        );
        memory
    }

    /// Prepare cached observations for a store without publishing a state.
    /// The boolean identifies lost knowledge requiring an origin marker in the
    /// completed result. Initialization records outlive discarded values.
    fn prepare_store_cache(
        &self,
        pointer: &Address,
        bytes: u32,
        assumptions: &PureFactContext,
        authorized_range: Option<&MemoryRange>,
    ) -> Option<(Self, bool)> {
        self.prepare_store_cache_of(pointer, bytes, bytes.into(), assumptions, authorized_range)
    }

    /// [`Self::prepare_store_cache`] for a store reaching `extent`: a whole
    /// object of abstract type is placed by the owner that holds it, as each
    /// such cell is, never by its bytes.
    fn prepare_store_cache_of(
        &self,
        pointer: &Address,
        bytes: u32,
        extent: crate::kernel::assumptions::AccessExtent,
        assumptions: &PureFactContext,
        authorized_range: Option<&MemoryRange>,
    ) -> Option<(Self, bool)> {
        let normalized_pointer = pointer.with_offset(
            normalize_exact_memory_loads_in_pointer_offset(&pointer.offset, assumptions),
        );
        // Computed once for the whole scan; the cells it is compared against
        // are the same-block ones, so the write's own atoms never change.
        let written = crate::kernel::reasoning::StoreByteInterval::of(&normalized_pointer, bytes);
        let mut memory = self.clone();
        // An overwritten value is stale, not forgotten: the store about to
        // run replaces exactly what was dropped, so the result still says
        // everything about the state it describes. A possibly aliasing value,
        // or one the store writes only part of, is knowledge the result no
        // longer has: it is `Forgotten`, which is what has to show in the
        // content, keeps automatic bytes initialized (see
        // `record_dropped_initialized_cells`), and ends a zero reading under it.
        // Every cell in a block proven distinct from the written one is kept
        // by each ladder below (its bytes are `Separate` and its address is
        // proven distinct on the first rung), so only the candidates are
        // asked.
        let candidates = AliasCandidates::of_block(&normalized_pointer.base);
        // Ownership first. A cell that a resource composition owns through a
        // different member than the written bytes is kept by the partition
        // law, whichever rung below would have found that out; asking it
        // first, through the composition's base index, spares such cells the
        // pure-fact distinctness ladder, whose failing searches cost work in
        // every separation fact of the block. Cells ownership does not place
        // go down the ladder unchanged.
        let owned_footprint = assumptions.owned_store_footprint(&normalized_pointer, extent);
        let mut run_forgot = false;
        let run_rule = |run: &CellRun| {
            let (kept, forgot) =
                crate::kernel::reasoning::memory_resolution::run_slots_kept_by_store(
                    run,
                    &normalized_pointer,
                    bytes,
                    assumptions,
                );
            run_forgot |= forgot;
            (kept, crate::kernel::primitives::RuleAnswer::Sound)
        };
        // Cells of the written block whose constant byte gap from the store
        // decides them are kept without being asked; the ladder below keeps
        // every one of them, reading no fact (see `reasoning::store_gap`).
        let gap_kept = crate::kernel::reasoning::store_gap::store_gap_kept_ranges(
            &normalized_pointer,
            bytes,
            assumptions,
        );
        // Objects a known address equality ties to the written one may share
        // the written bytes.
        let cell_fate = |cell_pointer: &Address, cell_value: &ProgramValue| {
            let normalized_cell_pointer = cell_pointer.with_offset(
                normalize_exact_memory_loads_in_pointer_offset(&cell_pointer.offset, assumptions),
            );
            if normalized_cell_pointer.base == normalized_pointer.base
                && written
                    .as_ref()
                    .is_some_and(|written| written.overwrites(&normalized_cell_pointer, cell_value))
            {
                // Only a cell the store writes *completely* is stale. One it
                // writes part of leaves the untouched bytes unrecorded, so the
                // result knows strictly less than its source and has to say so.
                return if written.as_ref().is_some_and(|written| {
                    written.overwrites_completely(&normalized_cell_pointer, cell_value)
                }) {
                    CachedValueFate::Overwritten
                } else {
                    CachedValueFate::Forgotten
                };
            }
            if assumptions
                .addresses_numerically_connected(&normalized_pointer, &normalized_cell_pointer)
            {
                return if crate::kernel::memory_history::indexed_store_byte_separation_evidence(
                    &normalized_pointer,
                    bytes,
                    &normalized_cell_pointer,
                    crate::kernel::reasoning::cell_access_byte_width(cell_value),
                    assumptions,
                )
                .is_some()
                {
                    CachedValueFate::Kept
                } else {
                    CachedValueFate::Forgotten
                };
            }
            if assumptions.access_owned_apart_from_store(
                &owned_footprint,
                &normalized_pointer,
                &normalized_cell_pointer,
                crate::kernel::assumptions::access_extent_of_value(cell_value),
            ) {
                return CachedValueFate::Kept;
            }
            // Distinct fields of one symbolic object, by the layout's rule.
            if crate::kernel::reasoning::memory_resolution::symbolic_fields_apart(
                &normalized_cell_pointer,
                crate::kernel::assumptions::access_extent_of_value(cell_value),
                &normalized_pointer,
                extent,
            ) {
                return CachedValueFate::Kept;
            }
            // A field of a symbolic object has no constant offset for the
            // address ladders below; a stated separation of its object from
            // the written bytes keeps it.
            if crate::kernel::SymbolicLayoutName::field_displacement(
                &normalized_cell_pointer.offset,
            )
            .is_some()
                && assumptions
                    .memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                        &MemoryRange::of_access(
                            &normalized_cell_pointer,
                            crate::kernel::assumptions::access_extent_of_value(cell_value),
                        ),
                        &MemoryRange::of_access(&normalized_pointer, extent),
                    )
            {
                return CachedValueFate::Kept;
            }
            let address_inequality_separates_bytes = crate::kernel::reasoning::access_byte_overlap(
                &normalized_cell_pointer,
                crate::kernel::assumptions::access_extent_of_value(cell_value),
                &normalized_pointer,
                extent,
                assumptions,
            )
                == crate::kernel::reasoning::AccessByteOverlap::Separate;
            let kept = address_inequality_separates_bytes
                && crate::kernel::reasoning::pointers_directly_distinct_for_store(
                    &normalized_cell_pointer,
                    &normalized_pointer,
                    assumptions,
                );
            if kept {
                CachedValueFate::Kept
            } else {
                CachedValueFate::Forgotten
            }
        };
        let view_fate = |cell_pointer: &Address, cell_type: ProgramType| {
            let normalized_cell_pointer = cell_pointer.with_offset(
                normalize_exact_memory_loads_in_pointer_offset(&cell_pointer.offset, assumptions),
            );
            if normalized_cell_pointer.base == normalized_pointer.base
                && written.as_ref().is_some_and(|written| {
                    written.overwrites_typed(&normalized_cell_pointer, cell_type)
                })
            {
                return if written.as_ref().is_some_and(|written| {
                    written.overwrites_typed_completely(&normalized_cell_pointer, cell_type)
                }) {
                    CachedValueFate::Overwritten
                } else {
                    CachedValueFate::Forgotten
                };
            }
            if assumptions
                .addresses_numerically_connected(&normalized_pointer, &normalized_cell_pointer)
            {
                return if crate::kernel::memory_history::indexed_store_byte_separation_evidence(
                    &normalized_pointer,
                    bytes,
                    &normalized_cell_pointer,
                    cell_type.byte_width().max(1),
                    assumptions,
                )
                .is_some()
                {
                    CachedValueFate::Kept
                } else {
                    CachedValueFate::Forgotten
                };
            }
            if assumptions.access_owned_apart_from_store(
                &owned_footprint,
                &normalized_pointer,
                &normalized_cell_pointer,
                cell_type.byte_width().max(1),
            ) {
                return CachedValueFate::Kept;
            }
            // A union view has no value to read a width from, so it stands in
            // the width of the type it is keyed by — the access it records.
            let address_inequality_separates_bytes = crate::kernel::reasoning::access_byte_overlap(
                &normalized_cell_pointer,
                cell_type.byte_width().max(1),
                &normalized_pointer,
                bytes,
                assumptions,
            )
                == crate::kernel::reasoning::AccessByteOverlap::Separate;
            let kept = address_inequality_separates_bytes
                && crate::kernel::reasoning::pointers_directly_distinct_for_store(
                    &normalized_cell_pointer,
                    &normalized_pointer,
                    assumptions,
                );
            if kept {
                CachedValueFate::Kept
            } else {
                CachedValueFate::Forgotten
            }
        };
        let ordered = authorized_range
            .and_then(|range| {
                memory.cells.parameter_store_candidates(
                    &normalized_pointer,
                    bytes,
                    &candidates,
                    &gap_kept,
                    assumptions,
                    Some(range),
                )
            })
            .map(|(cells, runs)| (cells, Some(runs)))
            .or_else(|| {
                memory
                    .cells
                    .ordered_store_candidates(
                        &normalized_pointer,
                        bytes,
                        &candidates,
                        assumptions,
                        None,
                    )
                    .map(|cells| (cells, None))
            })
            .or_else(|| {
                memory
                    .cells
                    .parameter_store_candidates(
                        &normalized_pointer,
                        bytes,
                        &candidates,
                        &gap_kept,
                        assumptions,
                        None,
                    )
                    .map(|(cells, runs)| (cells, Some(runs)))
            })
            .or_else(|| {
                // A pointer value reaches no local whose address is never
                // taken (`never_address_taken_local_versus_pointer_value`),
                // so a store through one asks only the cells a pointer can
                // reach, unless a stated equality places it in such a local.
                (matches!(normalized_pointer.base, AddressBase::Symbolic(_))
                    && !assumptions
                        .exact_pointer_aliases(&normalized_pointer)
                        .any(|alias| {
                            crate::kernel::primitives::block_is_never_address_taken_local(
                                &alias.base,
                            )
                        }))
                .then(|| (memory.cells.pointer_reachable_cells(), None))
            });
        let scope = match ordered.as_ref() {
            Some((selected, runs)) => ForgetScope::Ordered {
                candidates: &candidates,
                selected,
                cells_kept: &gap_kept,
                runs: runs.as_deref(),
            },
            None => ForgetScope::Candidates {
                candidates: &candidates,
                cells_kept: &gap_kept,
            },
        };
        let forgot_values = memory.forget_cached_values(
            scope,
            |pointer, value| match value {
                CachedValue::Cell(value) => cell_fate(pointer, value),
                CachedValue::UnionView(program_type, _) => view_fate(pointer, program_type),
            },
            run_rule,
        );
        let forgot_live_knowledge = forgot_values || run_forgot;
        // Forgetting nothing is not a transition: the memory is the same
        // state, so a later load keeps resolving through it unchanged
        // instead of stopping at an edge that records no write.
        if memory.cells.len() == self.cells.len()
            && memory.union_cells.len() == self.union_cells.len()
            && !forgot_values
        {
            return None;
        }
        Some((memory, forgot_live_knowledge))
    }

    /// Value-only parameters never own storage. Give their pseudo-slots a
    /// separate namespace so a caller's same-named local cannot supply a cell
    /// or be overwritten by a parameter assignment.
    pub(in crate::kernel) fn value_parameter_pointer(name: impl Into<BindingName>) -> Address {
        let name = name.into();
        let block = match name {
            BindingName::SliceLength(length) => AddressBase::SliceLength {
                slice: length,
                instance: LocalStorageInstance::ValueParameter,
            },
            BindingName::ReferenceCarrier(referent) => AddressBase::ReferenceCarrier {
                referent,
                instance: LocalStorageInstance::ValueParameter,
            },
            BindingName::Local(binding) => AddressBase::AutomaticLocal {
                binding,
                instance: LocalStorageInstance::ValueParameter,
            },
            BindingName::Static(binding) => AddressBase::StaticObject { binding },
            BindingName::Named(name) => format!("local:value-parameter:{name}").into(),
            BindingName::ContractResult
            | BindingName::ContractException
            | BindingName::Generated(_) => {
                unreachable!("contract outcome is not an automatic declaration")
            }
        };
        Address::new(block, AddressOffset::constant(0))
    }

    pub(in crate::kernel) fn local_pointer(name: impl Into<BindingName>) -> Address {
        let name = name.into();
        let block = match name {
            BindingName::SliceLength(length) => AddressBase::SliceLength {
                slice: length,
                instance: LocalStorageInstance::Implicit,
            },
            BindingName::ReferenceCarrier(referent) => AddressBase::ReferenceCarrier {
                referent,
                instance: LocalStorageInstance::Implicit,
            },
            BindingName::Local(binding) => AddressBase::AutomaticLocal {
                binding,
                instance: LocalStorageInstance::Implicit,
            },
            BindingName::Static(binding) => AddressBase::StaticObject { binding },
            BindingName::Named(name) => format!("local:{name}").into(),
            BindingName::Generated(_) => unreachable!("a logical binder has no storage"),
            BindingName::ContractResult => AddressBase::ContractResult,
            BindingName::ContractException => AddressBase::ContractException,
        };
        Address::new(block, AddressOffset::constant(0))
    }

    pub(in crate::kernel) fn local_lifetime_pointer(
        lifetime: u64,
        name: impl Into<BindingName>,
    ) -> Address {
        let name = name.into();
        let block = match name {
            BindingName::SliceLength(length) => AddressBase::SliceLength {
                slice: length,
                instance: LocalStorageInstance::Lifetime(lifetime),
            },
            BindingName::ReferenceCarrier(referent) => AddressBase::ReferenceCarrier {
                referent,
                instance: LocalStorageInstance::Lifetime(lifetime),
            },
            BindingName::Local(binding) => AddressBase::AutomaticLocal {
                binding,
                instance: LocalStorageInstance::Lifetime(lifetime),
            },
            BindingName::Static(binding) => AddressBase::StaticObject { binding },
            BindingName::Named(name) => format!("local:lifetime:{lifetime}:{name}").into(),
            BindingName::ContractResult
            | BindingName::ContractException
            | BindingName::Generated(_) => {
                unreachable!("contract outcome is not an automatic declaration")
            }
        };
        Address::new(block, AddressOffset::constant(0))
    }

    pub(crate) fn global_pointer(name: impl Into<BindingName>) -> Address {
        let block = match name.into() {
            BindingName::Static(binding) => AddressBase::StaticObject { binding },
            BindingName::Named(name) => format!("global:{name}").into(),
            BindingName::SliceLength(_)
            | BindingName::ReferenceCarrier(_)
            | BindingName::Local(_)
            | BindingName::ContractResult
            | BindingName::ContractException
            | BindingName::Generated(_) => {
                unreachable!("non-global binding used as a global")
            }
        };
        Address::new(block, AddressOffset::constant(0))
    }

    pub(crate) fn string_literal_pointer(identity: &StringLiteralId, bytes: &[u8]) -> Address {
        Address::new(
            AddressBase::StringLiteral {
                identity: identity.clone(),
                bytes: bytes.to_vec(),
            },
            AddressOffset::constant(0),
        )
    }

    pub(crate) fn static_pointer(function: &str, name: impl Into<BindingName>) -> Address {
        let block = match name.into() {
            BindingName::Static(binding) => AddressBase::StaticObject { binding },
            BindingName::Named(name) => format!("static:{function}:{name}").into(),
            BindingName::SliceLength(_)
            | BindingName::ReferenceCarrier(_)
            | BindingName::Local(_)
            | BindingName::ContractResult
            | BindingName::ContractException
            | BindingName::Generated(_) => {
                unreachable!("non-static binding used as a static")
            }
        };
        Address::new(block, AddressOffset::constant(0))
    }

    /// Materialized return storage has a typed identity, never a C local name.
    pub(in crate::kernel) fn aggregate_return_pointer(frame: u64) -> Address {
        Address::new(
            AddressBase::AggregateReturn { frame },
            AddressOffset::constant(0),
        )
    }

    pub(in crate::kernel) fn frame_local_pointer(
        frame: u64,
        name: impl Into<BindingName>,
    ) -> Address {
        match name.into() {
            BindingName::SliceLength(length) => Address::new(
                AddressBase::SliceLength {
                    slice: length,
                    instance: LocalStorageInstance::Frame(frame),
                },
                AddressOffset::constant(0),
            ),
            BindingName::ReferenceCarrier(referent) => Address::new(
                AddressBase::ReferenceCarrier {
                    referent,
                    instance: LocalStorageInstance::Frame(frame),
                },
                AddressOffset::constant(0),
            ),
            BindingName::Local(binding) => Address::new(
                AddressBase::AutomaticLocal {
                    binding,
                    instance: LocalStorageInstance::Frame(frame),
                },
                AddressOffset::constant(0),
            ),
            BindingName::Static(binding) => Address::new(
                AddressBase::StaticObject { binding },
                AddressOffset::constant(0),
            ),
            BindingName::ContractResult
            | BindingName::ContractException
            | BindingName::Generated(_) => {
                unreachable!("contract outcome is not a frame-local declaration")
            }
            BindingName::Named(name) => Address::new(
                format!("local:frame:{frame}:{name}").into(),
                AddressOffset::constant(0),
            ),
        }
    }

    pub(crate) fn has_block(&self, block: &AddressBase) -> bool {
        self.blocks.contains_key(block)
    }

    /// Whether this memory holds any storage that is not an automatic
    /// (`local:`) or havoc (`havoc:`) block: a named block or a live heap
    /// allocation. Stops at the first one.
    pub(crate) fn has_nonlocal_storage(&self) -> bool {
        !self.heap.live_allocations.is_empty()
            || self
                .blocks
                .keys()
                .any(|block| !block.is_local_block() && !block.is_havoc_block())
    }

    pub(in crate::kernel) fn is_ended_local_block(&self, block: &AddressBase) -> bool {
        self.forgotten.ended_local_blocks.contains(block)
    }

    /// Whether this memory and `other` are the same outside `blocks`: every
    /// block, cell, run and typed view on which they differ lies in one of
    /// `blocks`, and they agree on ended lifetimes, forget marks and the
    /// heap. Only the entries on which the two differ are visited.
    pub(in crate::kernel) fn differs_only_within(
        &self,
        other: &Self,
        blocks: &dyn BlockMembership,
    ) -> bool {
        self.forgotten == other.forgotten
            && self.heap == other.heap
            && self
                .blocks
                .diff(&other.blocks)
                .all(|change| blocks.contains_block(change.key()))
            && self.cells.differs_only_within(&other.cells, blocks)
            && self
                .union_cells
                .diff(&other.union_cells)
                .all(|change| blocks.contains_block(&change.key().0.base))
    }

    /// The automatic objects whose lifetimes this memory records as ended.
    pub(in crate::kernel) fn ended_local_blocks(&self) -> impl Iterator<Item = &AddressBase> {
        self.forgotten.ended_local_blocks.iter()
    }

    pub(in crate::kernel) fn is_ended_local_address(&self, pointer: &Address) -> bool {
        self.forgotten.ended_local_blocks.contains(&pointer.base)
    }

    /// Whether this memory has already given this block to an automatic
    /// object: one that is live, or one whose lifetime ended and whose
    /// tombstone still makes aliases to it invalid.
    ///
    /// Handing the same block to a second object would make the two one
    /// object at every site that reads `a.block == b.block`, so a declaration
    /// asks this before it mints.
    pub(in crate::kernel) fn local_block_is_occupied(&self, block: &AddressBase) -> bool {
        self.blocks.contains_key(block) || self.forgotten.ended_local_blocks.contains(block)
    }

    /// A sufficient, search-free condition for transporting loadability of
    /// an exact range. Unlike value equality, this ignores writes, but never
    /// ignores changed block sizes or allocation retirement metadata.
    pub(in crate::kernel) fn read_region_identity(&self, base: &Address) -> ReadRegionIdentity {
        crate::instrumentation::record_deterministic_work(1);
        let stored = crate::kernel::eval::pointer_read_over_immediate_store(base);
        let base = stored.as_ref().unwrap_or(base);
        ReadRegionIdentity {
            block_size: self.block_allocation_size(&base.base).cloned(),
            local_lifetime_ended: self.forgotten.ended_local_blocks.contains(&base.base),
            heap: self.heap.clone(),
        }
    }

    pub(in crate::kernel) fn has_call_memory_havoc(&self) -> bool {
        // Call-havoc markers are concrete blocks with this prefix. Bound the
        // B-tree query to that lexical interval so a load does not scan
        // unrelated memory blocks on the evaluator hot path.
        let first = AddressBase::Concrete("call-havoc:".to_string());
        let end = AddressBase::Concrete("call-havoc;".to_string());
        self.blocks.range(first..end).next().is_some()
    }

    pub(in crate::kernel) fn is_read_only_block(&self, block: &AddressBase) -> bool {
        self.blocks
            .get(block)
            .is_some_and(MemoryBlock::is_read_only)
    }

    pub(in crate::kernel) fn block_size(&self, block: &AddressBase) -> Option<&OldMachineTerm> {
        self.blocks.get(block).map(MemoryBlock::size)
    }

    /// The block's byte count with its format; see [`MemoryBlock::allocation_size`].
    pub(in crate::kernel) fn block_allocation_size(
        &self,
        block: &AddressBase,
    ) -> Option<&AllocationSize> {
        self.blocks.get(block).map(MemoryBlock::allocation_size)
    }

    pub(in crate::kernel) fn is_loadable_concretely(
        &self,
        pointer: &Address,
        byte_width: u32,
    ) -> bool {
        // Static read-only objects have complete initialization. Local
        // read-only objects can also be declared without an initializer.
        if self.is_read_only_block(&pointer.base)
            && (!pointer.base.is_local_block()
                || self.has_initialized_bytes_at(pointer, byte_width))
        {
            return self.access_in_bounds(pointer, byte_width);
        }
        // The width alone decides, so a run slot's value is not named: a
        // question about a slot's presence costs the same whatever the
        // run's length, and whether the value was named earlier.
        self.cells.value_width_at(pointer) == Some(byte_width)
    }

    pub(in crate::kernel) fn can_store_concretely(
        &self,
        pointer: &Address,
        value: &ProgramValue,
    ) -> bool {
        !self.is_read_only_block(&pointer.base)
            && (self.cells.contains_key(pointer)
                || self.access_extent_in_bounds(
                    pointer,
                    crate::kernel::assumptions::access_extent_of_value(value),
                ))
    }

    /// [`Self::access_in_bounds`] for an access reaching `extent`. In a block
    /// of a symbolic size, a field's access is inside its object by the
    /// layout's rule, found by lookup: at `offsetof(L, f)` in a block of
    /// `sizeof(L)`, reaching no further than `f`, or a whole value of `T`
    /// at the start of a block of `sizeof(T)`.
    pub(in crate::kernel) fn access_extent_in_bounds(
        &self,
        pointer: &Address,
        extent: crate::kernel::AccessExtent,
    ) -> bool {
        if let crate::kernel::AccessExtent::Bytes(bytes) = extent
            && self.access_in_bounds(pointer, bytes)
        {
            return true;
        }
        let Some(block) = self.blocks.get(&pointer.base) else {
            return false;
        };
        let size = block.size();
        match crate::kernel::SymbolicLayoutName::field_displacement(&pointer.offset) {
            Some((None, layout, field)) => {
                *size == layout.size_term() && layout.within_field(field, extent)
            }
            Some(_) => false,
            None => {
                pointer.offset.as_const() == Some(0)
                    && matches!(extent, crate::kernel::AccessExtent::Object(parameter)
                        if *size == parameter.size_term())
            }
        }
    }

    pub(in crate::kernel) fn access_in_bounds(&self, pointer: &Address, byte_width: u32) -> bool {
        let Some(offset) = pointer.offset.as_const() else {
            return false;
        };
        let Ok(offset) = u32::try_from(offset) else {
            return false;
        };
        let Some(block) = self.blocks.get(&pointer.base) else {
            return false;
        };
        let Some(block_size) = block.size().as_const() else {
            return false;
        };
        offset
            .checked_add(byte_width)
            .is_some_and(|end| end <= block_size)
    }

    /// The point a legacy symbolic read of this memory is named at: this
    /// memory, recording `site` as the read site when the caller has one.
    fn legacy_read_point(&self, site: &ProgramPoint) -> ProgramPoint {
        ProgramPoint::read_at(&crate::kernel::intern_memory(self.clone()), site)
    }

    #[cfg_attr(test, track_caller)]
    pub(in crate::kernel) fn symbolic_int32_load(
        &self,
        site: &ProgramPoint,
        pointer: &Address,
    ) -> ProgramValue {
        int32(crate::kernel::OldMachineTerm::read_named(
            self.legacy_read_point(site),
            pointer.clone(),
            LoadKind::Int32,
        ))
    }

    /// A signed byte read: the two's-complement conversion of the byte's
    /// one unsigned read ([`OldMachineTerm::memory_read`]).
    #[cfg_attr(test, track_caller)]
    pub(in crate::kernel) fn symbolic_int8_load(
        &self,
        site: &ProgramPoint,
        pointer: &Address,
    ) -> ProgramValue {
        int8(OldMachineTerm::read_named(
            self.legacy_read_point(site),
            pointer.clone(),
            LoadKind::Int8,
        ))
    }

    #[cfg_attr(test, track_caller)]
    pub(in crate::kernel) fn symbolic_int16_load(
        &self,
        site: &ProgramPoint,
        pointer: &Address,
    ) -> ProgramValue {
        int16(crate::kernel::OldMachineTerm::read_named(
            self.legacy_read_point(site),
            pointer.clone(),
            LoadKind::Int16,
        ))
    }

    #[cfg_attr(test, track_caller)]
    pub(in crate::kernel) fn symbolic_uint8_load(
        &self,
        site: &ProgramPoint,
        pointer: &Address,
    ) -> ProgramValue {
        uint8(crate::kernel::OldMachineTerm::read_named(
            self.legacy_read_point(site),
            pointer.clone(),
            LoadKind::UInt8,
        ))
    }

    #[cfg_attr(test, track_caller)]
    pub(in crate::kernel) fn symbolic_uint16_load(
        &self,
        site: &ProgramPoint,
        pointer: &Address,
    ) -> ProgramValue {
        uint16(crate::kernel::OldMachineTerm::read_named(
            self.legacy_read_point(site),
            pointer.clone(),
            LoadKind::UInt16,
        ))
    }

    #[cfg_attr(test, track_caller)]
    pub(in crate::kernel) fn symbolic_uint32_load(
        &self,
        site: &ProgramPoint,
        pointer: &Address,
    ) -> ProgramValue {
        uint32(crate::kernel::OldMachineTerm::read_named(
            self.legacy_read_point(site),
            pointer.clone(),
            LoadKind::UInt32,
        ))
    }

    #[cfg_attr(test, track_caller)]
    pub(in crate::kernel) fn symbolic_int64_load(
        &self,
        site: &ProgramPoint,
        pointer: &Address,
    ) -> ProgramValue {
        ProgramValue::Int64(crate::kernel::OldMachineTerm::read_named(
            self.legacy_read_point(site),
            pointer.clone(),
            LoadKind::Bits64,
        ))
    }

    /// The value of algebraic type `parameter` this memory holds at
    /// `pointer`, the counterpart of [`Self::symbolic_int64_load`] for the
    /// stand-in of an algebraic read.
    pub(in crate::kernel) fn symbolic_algebraic_load(
        &self,
        site: &ProgramPoint,
        pointer: &Address,
        parameter: crate::kernel::TypeParameterName,
    ) -> ProgramValue {
        crate::kernel::AlgebraicTermNode::parameter_load_at(
            self.legacy_read_point(site),
            pointer.clone(),
            parameter,
        )
    }

    #[cfg_attr(test, track_caller)]
    pub(in crate::kernel) fn symbolic_uint64_load(
        &self,
        site: &ProgramPoint,
        pointer: &Address,
    ) -> ProgramValue {
        ProgramValue::UInt64(crate::kernel::OldMachineTerm::read_named(
            self.legacy_read_point(site),
            pointer.clone(),
            LoadKind::Bits64,
        ))
    }

    #[cfg_attr(test, track_caller)]
    pub(in crate::kernel) fn symbolic_wide_integer_load(
        &self,
        pointer: &Address,
        ty: MachineIntegerType,
    ) -> Option<ProgramValue> {
        if ty.format().bits() != 128 {
            return None;
        }
        let load = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::unplaced(&(crate::kernel::intern_memory(self.clone()))),
            pointer.clone(),
            LoadKind::of_type(ty.program_type())?,
        );
        Some(match ty {
            MachineIntegerType::Int128 => ProgramValue::Int128(load),
            MachineIntegerType::UInt128 => ProgramValue::UInt128(load),
            _ => return None,
        })
    }

    pub(in crate::kernel) fn symbolic_float32_load(&self, pointer: &Address) -> ProgramValue {
        ProgramValue::Float32(crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::unplaced(&(crate::kernel::intern_memory(self.clone()))),
            pointer.clone(),
            LoadKind::Float32,
        ))
    }

    pub(in crate::kernel) fn symbolic_float64_load(&self, pointer: &Address) -> ProgramValue {
        ProgramValue::Float64(crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::unplaced(&(crate::kernel::intern_memory(self.clone()))),
            pointer.clone(),
            LoadKind::Float64,
        ))
    }

    /// [`Self::symbolic_pointer_load`] for a logical read: the pointer read
    /// is named by the cell's version ([`Address::version_read`]).
    pub(in crate::kernel) fn symbolic_pointer_version_load(
        &self,
        site: Option<&ProgramPoint>,
        pointer: &Address,
        value_type: ProgramType,
    ) -> ProgramValue {
        let retained_state = crate::kernel::intern_memory(self.clone());
        // A version read is a named read, or a value the memory holds for the
        // cell, either of which already carries its definition.
        match Address::version_read_value(&retained_state, site, pointer) {
            Ok(held) => ProgramValue::Pointer(held.with_type(value_type)),
            Err(value) => ProgramValue::Pointer(Pointer::from_read_at(
                value,
                value_type,
                &retained_state,
                site,
                pointer,
            )),
        }
    }

    /// The pointer read of `pointer` in this memory, recording `site` as the
    /// read site when the caller has one, as the scalar loads above do.
    pub(in crate::kernel) fn symbolic_pointer_load(
        &self,
        site: Option<&ProgramPoint>,
        pointer: &Address,
        value_type: ProgramType,
    ) -> ProgramValue {
        let retained_state = crate::kernel::intern_memory(self.clone());
        let value = Address::loaded(&crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::read_at_optional(&retained_state, site),
            pointer.clone(),
            LoadKind::Int32,
        ))
        .expect("a memory load names its read");
        // This factory constructs an exact typed read, just like the seeded
        // cell producer. Keep its defining state and address even when a
        // resource argument evaluator does not retain a C load's fact stream.
        crate::kernel::equality_graph::EqualityGraph::default()
            .register_pointer_read_definition_at(&value, &retained_state, site, pointer);
        ProgramValue::Pointer(Pointer::from_read_at(
            value,
            value_type,
            &retained_state,
            site,
            pointer,
        ))
    }
}

impl ExecutionState {
    /// The read named by a local that holds an abstract or enum value in
    /// memory. The indexed write supplies its version when available. A
    /// certified observation can otherwise name an opaque type parameter
    /// at the current program point.
    pub fn held_local_value(&self, name: impl Into<BindingName>) -> Option<ProgramValue> {
        let name = name.into();
        let (ProgramType::Parameter(value_type), slot) = self.locals().held_value_local(&name)?
        else {
            return None;
        };
        let point = self.program_point();
        let version = point.abstract_local_version(slot, value_type).or_else(|| {
            (value_type.has_abstract_size() && point.has_certified_read_view())
                .then(|| point.clone().for_exact_read())
        });
        if let Some(version) = version {
            return Some(AlgebraicTermNode::parameter_load_at(
                version,
                slot.clone(),
                value_type,
            ));
        }
        Some(AlgebraicTermNode::parameter_load(
            crate::kernel::intern_memory_ref(self.memory()),
            &point,
            slot.clone(),
            value_type,
        ))
    }

    /// The first part of `self` that differs from `other`, named for a
    /// diagnostic, or `None` when the states are equal. A differing resource
    /// context names a resource fact held on one side only; every other part
    /// is named by what it is.
    #[cfg(test)]
    pub(crate) fn first_difference(&self, other: &ExecutionState) -> Option<String> {
        if self.resources != other.resources {
            let only_in = |left: &ResourceContext, right: &ResourceContext| {
                left.facts()
                    .iter()
                    .find(|fact| !right.facts().contains(fact))
                    .map(ResourceFact::diagnostic_summary)
            };
            return Some(match only_in(&self.resources, &other.resources) {
                Some(fact) => format!("`{fact}` is held only before the rewrite"),
                None => match only_in(&other.resources, &self.resources) {
                    Some(fact) => format!("`{fact}` is held only in the published state"),
                    None => "the resource facts are held in a different representation".to_string(),
                },
            });
        }
        let parts: [(&str, bool); 23] = [
            ("memory", self.memory != other.memory),
            ("the local variables", self.locals != other.locals),
            (
                "the resource bindings",
                self.resource_bindings != other.resource_bindings,
            ),
            (
                "the instance field scope",
                self.instance_field_scope != other.instance_field_scope,
            ),
            (
                "the body field view",
                self.body_field_view != other.body_field_view,
            ),
            (
                "the aggregate destination",
                self.aggregate_destination != other.aggregate_destination,
            ),
            (
                "the borrow ledger",
                self.borrow_ledger != other.borrow_ledger,
            ),
            (
                "the borrow participant",
                self.borrow_participant != other.borrow_participant,
            ),
            (
                "the borrow view bindings",
                self.borrow_bindings != other.borrow_bindings,
            ),
            (
                "the thread ledger",
                self.thread_ledger != other.thread_ledger,
            ),
            ("the mutex ledger", self.mutex_ledger != other.mutex_ledger),
            (
                "the mutex protocol mode",
                self.preserves_mutex_protocols != other.preserves_mutex_protocols,
            ),
            (
                "the mutex input reservations",
                self.mutex_input_reservations != other.mutex_input_reservations,
            ),
            (
                "the opaque mutex acquisitions",
                self.opaque_mutex_acquisitions != other.opaque_mutex_acquisitions,
            ),
            (
                "the named mutex authorities",
                self.named_mutex_authorities != other.named_mutex_authorities,
            ),
            (
                "the pending thread creation",
                self.pending_thread_create != other.pending_thread_create,
            ),
            (
                "the population access",
                self.population_access != other.population_access,
            ),
            (
                "the observed population families",
                self.observed_population_families != other.observed_population_families,
            ),
            (
                "the population effects",
                self.population_effects != other.population_effects,
            ),
            (
                "the next stack frame identity",
                self.next_local_frame != other.next_local_frame,
            ),
            (
                "the next automatic-storage identity",
                self.next_local_lifetime != other.next_local_lifetime,
            ),
            (
                "whether an enclosing frame holds locals",
                self.enclosing_frame_holds_locals != other.enclosing_frame_holds_locals,
            ),
            ("the state", self != other),
        ];
        parts
            .into_iter()
            .find(|(_, differs)| *differs)
            .map(|(part, _)| format!("{part} differs"))
    }

    /// Selects a call destination without allocating, initializing, or granting
    /// authority. Function entry validates it against the construction layout.
    pub fn with_aggregate_return_destination(
        mut self,
        pointer: Address,
        layout: AggregateLayout,
    ) -> Self {
        self.aggregate_destination = Some(Arc::new(AggregateDestination { pointer, layout }));
        self
    }

    /// O(1), fail-closed comparison of the non-memory part of a predicate's
    /// state argument. The caller has already checked exact interned memory
    /// identity. Independently built empty environments are equivalent, but
    /// nonempty environments must share persistent storage.
    pub(crate) fn shares_non_memory_storage_with(&self, other: &Self) -> bool {
        fn same_or_empty_persistent_map<K: Ord, V>(
            left: &crate::persistent::PersistentMap<K, V>,
            right: &crate::persistent::PersistentMap<K, V>,
        ) -> bool {
            left.shares_root_with(right) || (left.is_empty() && right.is_empty())
        }
        let same_or_empty_resources = |left: &ResourceContext, right: &ResourceContext| {
            (std::sync::Arc::ptr_eq(&left.storage, &right.storage)
                && std::sync::Arc::ptr_eq(&left.borrow_dependencies, &right.borrow_dependencies))
                || (left.is_pristine_semantically_empty() && right.is_pristine_semantically_empty())
        };
        let same_bindings = match (&self.resource_bindings, &other.resource_bindings) {
            (None, None) => true,
            (Some(left), Some(right)) => {
                std::sync::Arc::ptr_eq(left, right) || (left.is_empty() && right.is_empty())
            }
            _ => false,
        };
        self.population_effects
            .predicate_count_permissions
            .is_some()
            == other
                .population_effects
                .predicate_count_permissions
                .is_some()
            && same_bindings
            && same_or_empty_persistent_map(&self.locals.bindings, &other.locals.bindings)
            && same_or_empty_persistent_map(&self.locals.slots, &other.locals.slots)
            && same_or_empty_resources(&self.instance_field_scope, &other.instance_field_scope)
            && self.body_field_view == other.body_field_view
            && same_or_empty_resources(&self.resources, &other.resources)
            && self.borrow_ledger == other.borrow_ledger
            && self.borrow_participant == other.borrow_participant
            && self.borrow_bindings == other.borrow_bindings
            && self.thread_ledger == other.thread_ledger
            && self.mutex_ledger == other.mutex_ledger
            && self.preserves_mutex_protocols == other.preserves_mutex_protocols
            && self.mutex_input_reservations == other.mutex_input_reservations
            && self.opaque_mutex_acquisitions == other.opaque_mutex_acquisitions
            && self.named_mutex_authorities == other.named_mutex_authorities
            && self.population_access == other.population_access
            && self.population_effects.creation == other.population_effects.creation
            && self.pending_thread_create == other.pending_thread_create
            && (self
                .observed_population_families
                .shares_storage_with(&other.observed_population_families)
                || (self.observed_population_families.is_empty()
                    && other.observed_population_families.is_empty()))
            && self.next_local_frame == other.next_local_frame
            && match (&self.aggregate_destination, &other.aggregate_destination) {
                (None, None) => true,
                (Some(left), Some(right)) => Arc::ptr_eq(left, right),
                _ => false,
            }
            && self.next_local_lifetime == other.next_local_lifetime
            && self.enclosing_frame_holds_locals == other.enclosing_frame_holds_locals
    }

    pub(crate) fn resource_instance_at_path(
        &self,
        identity: impl Into<InstanceRef>,
        children: &[String],
    ) -> Option<&ResourceInstance> {
        let identity = identity.into();
        if children.is_empty() {
            return self.resource_instance_fields(identity);
        }
        self.resources
            .owned_instance(self.resource_path_identity(identity, children)?)
    }

    /// Resolve an exposed slot from the retained opening, independently of
    /// whether the child is currently folded. This does not grant ownership.
    pub(crate) fn resource_path_identity(
        &self,
        identity: impl Into<InstanceRef>,
        children: &[String],
    ) -> Option<InstanceId> {
        let mut identity = match identity.into() {
            InstanceRef::Body => self.resource_bindings.as_ref()?.body()?,
            InstanceRef::Instance(identity) => self.bound_instance(identity)?,
        };
        for slot in children {
            crate::instrumentation::record_deterministic_work(1);
            if self.resources.owned_instance(identity).is_some() {
                return None;
            }
            let InstanceConsumption::Opened { children, .. } =
                self.resources.instance_consumption(identity)?
            else {
                return None;
            };
            identity = *children.get(slot)?;
        }
        Some(identity)
    }

    pub(crate) fn opened_resource_at_path(
        &self,
        identity: impl Into<InstanceRef>,
        children: &[String],
    ) -> Option<&ResourceInstance> {
        let identity = self.resource_path_identity(identity, children)?;
        match self.resources.instance_consumption(identity)? {
            InstanceConsumption::Opened { instance, .. } => Some(instance),
            _ => None,
        }
    }

    pub(crate) fn resource_witness(
        &self,
        identity: InstanceRef,
        children: &[String],
        name: &str,
    ) -> Option<&ProgramValue> {
        let identity = self.resource_path_identity(identity, children)?;
        if self.resources.owned_instance(identity).is_some() {
            return None;
        }
        match self.resources.instance_consumption(identity)? {
            InstanceConsumption::Opened { values, .. } => values.get(name),
            _ => None,
        }
    }

    /// Model reads may use an opening's captured fields. Resource operations
    /// use the separate live-instance lookup.
    pub(crate) fn projected_resource_field(
        &self,
        identity: InstanceRef,
        children: &[String],
        field_index: usize,
        field_name: Option<&str>,
    ) -> Option<(&ResourceInstance, usize)> {
        if children.is_empty() {
            return self
                .resource_instance_fields(identity)
                .or_else(|| self.opened_resource_at_path(identity, &[]))
                .map(|instance| (instance, field_index));
        }
        let mut identity = self.resource_path_identity(identity, &[])?;
        let field = field_name?;
        for (index, slot) in children.iter().enumerate() {
            crate::instrumentation::record_deterministic_work(1);
            let held = self
                .resources
                .owned_instance(identity)
                .or_else(|| self.instance_field_scope.owned_instance(identity));
            match held
                .is_none()
                .then(|| self.resources.instance_consumption(identity))
                .flatten()
            {
                Some(InstanceConsumption::Opened { children, .. }) => {
                    identity = *children.get(slot)?;
                }
                _ => {
                    let instance = held?;
                    let field = children[index..]
                        .iter()
                        .map(String::as_str)
                        .chain(std::iter::once(field))
                        .collect::<Vec<_>>()
                        .join(".");
                    let index = instance
                        .schema()
                        .fields()
                        .iter()
                        .position(|(name, _)| *name == field)?;
                    return Some((instance, index));
                }
            }
        }
        let instance = self.resources.owned_instance(identity).or_else(|| {
            match self.resources.instance_consumption(identity)? {
                InstanceConsumption::Opened { instance, .. } => Some(instance.as_ref()),
                _ => None,
            }
        })?;
        let index = instance
            .schema()
            .fields()
            .iter()
            .position(|(name, _)| name == field)?;
        Some((instance, index))
    }
    /// The caller instance a call-local instance binder names.
    fn bound_instance(&self, identity: InstanceId) -> Option<InstanceId> {
        match &self.resource_bindings {
            Some(bindings) => bindings.instance(identity),
            None => Some(identity),
        }
    }
    /// The instance a field read names. [`InstanceRef::Body`] is the opened
    /// instance its body binding names, or else the field view of a
    /// definition evaluated without one.
    pub(crate) fn resource_instance_fields(
        &self,
        identity: impl Into<InstanceRef>,
    ) -> Option<&ResourceInstance> {
        let actual = match identity.into() {
            InstanceRef::Body => {
                match self
                    .resource_bindings
                    .as_ref()
                    .and_then(|bindings| bindings.body())
                {
                    Some(actual) => actual,
                    None => return self.body_field_view.as_deref(),
                }
            }
            InstanceRef::Instance(identity) => self.bound_instance(identity)?,
        };
        self.resources
            .owned_instance(actual)
            .or_else(|| self.instance_field_scope.owned_instance(actual))
    }
    /// The owned instance a reference names. [`InstanceRef::Body`] names
    /// only an opened instance: a definition's field view is never owned.
    pub(crate) fn owned_resource_instance(
        &self,
        identity: impl Into<InstanceRef>,
    ) -> Option<&ResourceInstance> {
        let actual = match identity.into() {
            InstanceRef::Body => self.resource_bindings.as_ref()?.body()?,
            InstanceRef::Instance(identity) => self.bound_instance(identity)?,
        };
        self.resources.owned_instance(actual)
    }
    pub(crate) fn resolve_named_mutex_authority(
        &self,
        identity: MutexAuthorityId,
    ) -> Option<&ResourceFact> {
        self.named_mutex_authorities
            .as_ref()?
            .resolve(identity, self)
    }

    pub(in crate::kernel) fn bind_named_mutex_authority(
        mut self,
        identity: MutexAuthorityId,
        fact: &ResourceFact,
    ) -> Result<Self, super::super::named_authority::NamedMutexAuthorityError> {
        let current = self
            .named_mutex_authorities
            .as_ref()
            .map(|aliases| aliases.as_ref().clone())
            .unwrap_or_else(super::super::named_authority::NamedMutexAuthorities::new);
        let next = current.bind(identity, fact, &self)?;
        self.named_mutex_authorities = Some(Arc::new(next));
        Ok(self)
    }

    pub(in crate::kernel) fn rebind_named_mutex_authority(
        mut self,
        identity: MutexAuthorityId,
        expected: &ResourceFact,
    ) -> Result<Self, super::super::named_authority::NamedMutexAuthorityError> {
        let current = self
            .named_mutex_authorities
            .as_ref()
            .ok_or(super::super::named_authority::NamedMutexAuthorityError::NotBound)?;
        let next = current.rebind_existing_exact(identity, expected, &self)?;
        self.named_mutex_authorities = Some(Arc::new(next));
        Ok(self)
    }
    pub(in crate::kernel) fn transport_named_mutex_use(
        mut self,
        identity: MutexAuthorityId,
        source: &ResourceFact,
        derived: &ResourceFact,
    ) -> Result<Self, super::super::named_authority::NamedMutexAuthorityError> {
        let current = self
            .named_mutex_authorities
            .as_ref()
            .ok_or(super::super::named_authority::NamedMutexAuthorityError::NotBound)?;
        let next = current.transport_checked_use(identity, source, derived, &self)?;
        self.named_mutex_authorities = Some(Arc::new(next));
        Ok(self)
    }
    pub fn new() -> Self {
        Self::default()
    }

    pub(in crate::kernel) fn next_local_frame(&self) -> u64 {
        self.next_local_frame
    }

    /// Initialize the checked creation ledger only at a fresh source proof
    /// entry, before any C statement executes.
    pub(crate) fn with_population_creation_tracking(mut self) -> Self {
        if self.population_effects.creation.is_none() {
            Arc::make_mut(&mut self.population_effects).creation =
                Some(super::super::population_authority::storage_creation::CreationEvents::new());
        }
        self
    }

    /// Equality that also identifies two creation ledgers recording nothing.
    /// Separately built entry states for one contract differ only in their
    /// fresh ledger names, which nothing else in the state refers to.
    pub(crate) fn equal_up_to_unused_creation_ledgers(&self, other: &Self) -> bool {
        if self == other {
            return true;
        }
        let (Some(left), Some(right)) = (
            self.population_effects.creation.as_ref(),
            other.population_effects.creation.as_ref(),
        ) else {
            return false;
        };
        if !left.records_nothing() || !right.records_nothing() {
            return false;
        }
        let mut renamed = self.clone();
        Arc::make_mut(&mut renamed.population_effects).creation = Some(right.clone());
        renamed == *other
    }

    /// Equality that also identifies two creation ledgers recording the same
    /// state under different fresh identities or fresh storage anchors. Every
    /// other component is
    /// still compared exactly, so a component naming either identity keeps
    /// the states apart.
    pub(crate) fn equal_up_to_creation_ledger_identity(&self, other: &Self) -> bool {
        if self.equal_up_to_unused_creation_ledgers(other) {
            return true;
        }
        let (Some(left), Some(right)) = (
            self.population_effects.creation.as_ref(),
            other.population_effects.creation.as_ref(),
        ) else {
            return false;
        };
        if left == right
            || !(left.records_same_state_as(right)
                || left.records_same_state_up_to_fresh_anchors(right))
        {
            return false;
        }
        let mut renamed = self.clone();
        Arc::make_mut(&mut renamed.population_effects).creation = Some(right.clone());
        renamed == *other
    }

    /// Admit exactly one explicitly owned helper input as an opaque existing
    /// population. Its observable entry total is arbitrary, with no creator right.
    pub(crate) fn import_opaque_population(
        &self,
        authority: &ResourceFact,
        owned_members: u32,
    ) -> Result<Self, String> {
        let ResourceFact::Own(Resource::PopulationAuthority(description), quantity) = authority
        else {
            return Err("opaque import requires owns authority(R(p))".into());
        };
        if quantity.as_const() != Some(1)
            || !self.resources.contains_exact_representation(authority)
        {
            return Err("opaque import requires one declared owned authority".into());
        }
        if owned_members > 1 {
            return Err("opaque import supports at most one declared member".into());
        }
        if owned_members == 1 {
            let member = ResourceFact::own(Resource::Composite {
                name: description.family().to_owned(),
                arguments: description.arguments().to_vec().into(),
            });
            if !self.resources.contains_exact_representation(&member) {
                return Err("opaque import requires the declared owned member".into());
            }
        }
        let events = self
            .population_effects
            .creation
            .as_ref()
            .ok_or("opaque import requires the creation ledger")?
            .import_observable_contract_population(description, owned_members)
            .map_err(|refusal| format!("opaque population import refused: {refusal}"))?;
        let mut next = self.clone();
        Arc::make_mut(&mut next.population_effects).creation = Some(events);
        Ok(next)
    }

    pub(crate) fn import_opaque_population_inputs(
        &self,
        authority: &ResourceFact,
    ) -> Result<Self, String> {
        let Resource::PopulationAuthority(description) = authority.resource() else {
            return Err("population import requires authority".into());
        };
        if !description.schema().is_fieldless() {
            if authority.owned_quantity() != Some(1)
                || !self.resources.contains_exact_representation(authority)
            {
                return Err("Requires one declared owned authority for named members".into());
            }
            let events = self
                .population_effects
                .creation
                .as_ref()
                .ok_or("opaque import requires the creation ledger")?
                .import_observable_named_authority(description)
                .map_err(|refusal| format!("named authority import refused: {refusal}"))?;
            let mut next = self.clone();
            Arc::make_mut(&mut next.population_effects).creation = Some(events);
            return Ok(next);
        }
        let member = ResourceFact::own(Resource::Composite {
            name: description.family().to_owned(),
            arguments: description.arguments().to_vec().into(),
        });
        let held = self
            .resources
            .exact_resource_facts(member.resource())
            .into_iter()
            .filter(|fact| fact.owned_quantity_term().is_some())
            .collect::<Vec<_>>();
        if let [held] = held.as_slice() {
            self.import_opaque_population_quantity(authority, held)
        } else if held.len() > 1
            && let Some(total) = held.iter().try_fold(0u32, |total, fact| {
                fact.owned_quantity()
                    .and_then(|quantity| total.checked_add(quantity))
            })
        {
            // Separate contract clauses, such as a retained `owns` member
            // beside a `consumes` batch, are one custody of their summed units.
            if authority.owned_quantity() != Some(1)
                || !self.resources.contains_exact_representation(authority)
            {
                return Err(
                    "batch import requires this authority's exact declared owned quantity".into(),
                );
            }
            let events = self
                .population_effects
                .creation
                .as_ref()
                .ok_or("batch import requires the creation ledger")?
                .import_observable_contract_population_quantity(
                    description,
                    &OldMachineTerm::constant(total),
                )
                .map_err(|refusal| format!("batch population import refused: {refusal}"))?;
            let mut next = self.clone();
            Arc::make_mut(&mut next.population_effects).creation = Some(events);
            Ok(next)
        } else {
            self.import_opaque_population(
                authority,
                u32::from(self.resources.contains_exact_representation(&member)),
            )
        }
    }

    /// Retain the exact held batch as custody, independent of its arbitrary
    /// global entry total. No population creation occurs at helper entry.
    pub(crate) fn import_opaque_population_quantity(
        &self,
        authority: &ResourceFact,
        member: &ResourceFact,
    ) -> Result<Self, String> {
        let ResourceFact::Own(Resource::PopulationAuthority(description), authority_quantity) =
            authority
        else {
            return Err("batch import requires owned authority".into());
        };
        let ResourceFact::Own(Resource::Composite { name, arguments }, quantity) = member else {
            return Err("batch import requires an owned declared member quantity".into());
        };
        if authority_quantity.as_const() != Some(1)
            || name != description.family()
            || arguments != description.arguments()
            || !self.resources.contains_exact_representation(authority)
            || !self.resources.contains_exact_representation(member)
        {
            return Err(
                "batch import requires this authority's exact declared owned quantity".into(),
            );
        }
        let events = self
            .population_effects
            .creation
            .as_ref()
            .ok_or("batch import requires the creation ledger")?
            .import_observable_contract_population_quantity(description, quantity.old_form())
            .map_err(|refusal| format!("batch population import refused: {refusal}"))?;
        let mut next = self.clone();
        Arc::make_mut(&mut next.population_effects).creation = Some(events);
        Ok(next)
    }

    /// Import exactly the authority and identified member declared at a
    /// wildcard helper entry. Neither input is a population creation event.
    pub(crate) fn import_opaque_wildcard_population(
        &self,
        authority: &ResourceFact,
        member: &ResourceFact,
    ) -> Result<Self, String> {
        let ResourceFact::Own(Resource::PopulationAuthority(scope), quantity) = authority else {
            return Err("Requires owns authority(R(anchor, _))".into());
        };
        let ResourceFact::Own(Resource::Composite { name, arguments }, member_quantity) = member
        else {
            return Err("Requires owns R(anchor, member)".into());
        };
        if quantity.as_const() != Some(1)
            || member_quantity.as_const() != Some(1)
            || !self.resources.contains_exact_representation(authority)
            || !self.resources.contains_exact_representation(member)
        {
            return Err("Requires one owned authority and its declared owned member".into());
        }
        let description = super::super::ResourceDescription::new(
            name.clone(),
            arguments.clone(),
            super::super::ResourceFieldSchema::new(vec![]).expect("empty resource schema"),
        );
        let events = self
            .population_effects
            .creation
            .as_ref()
            .ok_or("opaque import requires the creation ledger")?
            .import_opaque_wildcard_population(scope, &description)
            .map_err(|refusal| format!("wildcard population import refused: {refusal}"))?;
        let mut next = self.clone();
        Arc::make_mut(&mut next.population_effects).creation = Some(events);
        Ok(next)
    }

    pub(crate) fn import_opaque_wildcard_authority(
        &self,
        authority: &ResourceFact,
    ) -> Result<Self, String> {
        let ResourceFact::Own(Resource::PopulationAuthority(scope), quantity) = authority else {
            return Err("Requires owns authority(R(anchor, _))".into());
        };
        if quantity.as_const() != Some(1)
            || !self.resources.contains_exact_representation(authority)
        {
            return Err("Requires one declared owned authority".into());
        }
        if !scope.schema().is_fieldless() {
            return self.import_opaque_population_inputs(authority);
        }
        let events = self
            .population_effects
            .creation
            .as_ref()
            .ok_or("opaque import requires the creation ledger")?
            .import_opaque_wildcard_authority(scope)
            .map_err(|refusal| format!("wildcard authority import refused: {refusal}"))?;
        let mut next = self.clone();
        Arc::make_mut(&mut next.population_effects).creation = Some(events);
        Ok(next)
    }

    pub(crate) fn with_checked_current_control_wrapper(
        &self,
        selected: &ResourceFact,
        definition: &super::super::CompositeResourceDefinition,
        assumptions: &PureFactContext,
    ) -> Result<Self, String> {
        let events = self
            .population_effects
            .creation
            .as_ref()
            .ok_or("control registration requires the creation ledger")?
            .checked_current_control_wrapper(self, selected, definition, assumptions)?;
        let mut next = self.clone();
        Arc::make_mut(&mut next.population_effects).creation = Some(events);
        Ok(next)
    }

    /// Contract lowering may name an established real population or the one
    /// opaque population explicitly imported from a standalone proof's entry.
    pub(crate) fn recognizes_population_authority(
        &self,
        description: &super::super::ResourceDescription,
    ) -> bool {
        self.population_effects
            .creation
            .as_ref()
            .is_some_and(|events| events.recognizes_population_authority(description))
    }

    /// Whether an exact resource belongs to an established or imported population.
    /// Wrapping such a resource's body must use the population exchange law.
    pub(crate) fn tracks_authority_member(&self, selected: &ResourceFact) -> bool {
        let Resource::Composite { name, arguments } = selected.resource() else {
            return false;
        };
        let description = super::super::ResourceDescription::new(
            name.clone(),
            arguments.clone(),
            super::super::ResourceFieldSchema::new(vec![]).expect("empty schema"),
        );
        self.population_effects
            .creation
            .as_ref()
            .is_some_and(|events| {
                events.tracks_population(&description)
                    || events.recognizes_imported_population(&description)
            })
    }

    /// Project the exact body of a folded, field-free control resource for
    /// checking its current facts. This does not publish the projection: the
    /// resource-rewrite certificate independently checks the eventual exchange.
    pub(crate) fn checked_authority_wrapper_projection(
        &self,
        selected: &ResourceFact,
        definition: &super::super::CompositeResourceDefinition,
        assumptions: &PureFactContext,
    ) -> Result<(ResourceContext, Vec<OldMachineTerm>), String> {
        self.authority_wrapper_fact_projection(selected, definition, assumptions, true)
    }

    /// Closing an open control checks actual owned children, not its suspended
    /// invariant. This projection grants custody reads and publishes no facts.
    pub(crate) fn checked_authority_wrapper_closing_projection(
        &self,
        selected: &ResourceFact,
        definition: &super::super::CompositeResourceDefinition,
        assumptions: &PureFactContext,
    ) -> Result<(ResourceContext, Vec<OldMachineTerm>), String> {
        self.authority_wrapper_fact_projection(selected, definition, assumptions, false)
    }

    fn authority_wrapper_fact_projection(
        &self,
        selected: &ResourceFact,
        definition: &super::super::CompositeResourceDefinition,
        assumptions: &PureFactContext,
        require_folded: bool,
    ) -> Result<(ResourceContext, Vec<OldMachineTerm>), String> {
        let (children, count) =
            self.authority_wrapper_body(selected, definition, assumptions, require_folded)?;
        // Retire the head before composing its body. Its ownership observations
        // can otherwise coalesce with a child and retire that child's access.
        let mut projected = self.resources.clone();
        if projected.satisfies_fact(selected, assumptions) {
            projected = projected
                .without_fact_incrementally(selected, assumptions)
                .ok_or("control fact projection lost its checked head")?;
        }
        // An open body may already hold these children. Reuse that custody;
        // composing it twice would duplicate exclusive allocation/authority.
        let missing = children
            .into_iter()
            .filter(|child| !projected.satisfies_fact(child, assumptions))
            .collect::<Vec<_>>();
        let projected = projected
            .install_established_partition(missing, assumptions)
            .map(|(context, _)| context)
            .map_err(|error| format!("control body ownership refused: {error}"))?;
        Ok((projected, count))
    }

    pub(crate) fn checked_authority_wrapper_body(
        &self,
        selected: &ResourceFact,
        definition: &super::super::CompositeResourceDefinition,
        assumptions: &PureFactContext,
    ) -> Result<(Vec<ResourceFact>, Vec<OldMachineTerm>), String> {
        self.authority_wrapper_body(selected, definition, assumptions, true)
    }

    /// Describe a selected control's declared authorities for exit checking.
    /// Unlike opening its body, this grants no ownership or count observations.
    pub(in crate::kernel) fn authority_wrapper_descriptions(
        &self,
        selected: &ResourceFact,
        definition: &super::super::CompositeResourceDefinition,
        assumptions: &PureFactContext,
    ) -> Result<Vec<ResourceDescription>, String> {
        self.authority_wrapper_candidates(selected, definition, assumptions, false)
            .map(|(_, descriptions)| descriptions)
    }

    /// Before a fold, require the exact body already owned. The certificate
    /// still checks the resulting exchange; this preflight only refuses a
    /// fold whose body is not yet owned.
    pub(crate) fn checked_authority_wrapper_fold_preflight(
        &self,
        selected: &ResourceFact,
        definition: &super::super::CompositeResourceDefinition,
        assumptions: &PureFactContext,
    ) -> Result<Vec<OldMachineTerm>, String> {
        let (_, count) = self.authority_wrapper_body(selected, definition, assumptions, false)?;
        Ok(count)
    }

    fn authority_wrapper_body(
        &self,
        selected: &ResourceFact,
        definition: &super::super::CompositeResourceDefinition,
        assumptions: &PureFactContext,
        require_folded: bool,
    ) -> Result<(Vec<ResourceFact>, Vec<OldMachineTerm>), String> {
        let (children, descriptions) =
            self.authority_wrapper_candidates(selected, definition, assumptions, require_folded)?;
        let counts = self.authority_counts_for_descriptions(descriptions)?;
        Ok((children, counts))
    }

    /// Connect newly emitted authority descriptions to the live ledger. This
    /// grants no authority and never re-evaluates the producing body.
    pub(in crate::kernel) fn returned_authority_counts(
        &self,
        authorities: &[ResourceFact],
    ) -> Result<Vec<OldMachineTerm>, String> {
        let descriptions = authorities
            .iter()
            .map(|fact| match fact.resource() {
                Resource::PopulationAuthority(description) => Ok(description.clone()),
                _ => Err("expected an emitted authority".into()),
            })
            .collect::<Result<Vec<_>, String>>()?;
        self.authority_counts_for_descriptions(descriptions)
    }

    fn authority_counts_for_descriptions(
        &self,
        descriptions: Vec<ResourceDescription>,
    ) -> Result<Vec<OldMachineTerm>, String> {
        let mut counts = Vec::with_capacity(descriptions.len());
        for description in descriptions {
            let Some([crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(pointer))]) =
                (description.arguments()).fixed_values::<1>()
            else {
                return Err("control authority needs one pointer anchor".into());
            };
            let anchor = pointer.address();
            let events = self
                .population_effects
                .creation
                .as_ref()
                .ok_or("control resource requires the creation ledger")?;
            if !events.owns_population_authority(&description) {
                return Err("Requires owns authority(R(p))".into());
            }
            let external = is_external_population_anchor(anchor);
            let count = if !external && matches!(anchor.offset.view(), OffsetView::Constant(0)) {
                events
                    .observe_term(&anchor.base, description.family())
                    .map_err(|_| "Requires a current authority count")?
            } else {
                let imported = events
                    .observe_symbolic(&description)
                    .ok_or("Requires a current authority count")?;
                if let Some((produce, quantity)) = imported.combined_delta() {
                    if produce {
                        OldMachineTerm::add(imported.entry_count, quantity)
                    } else {
                        OldMachineTerm::subtract(imported.entry_count, quantity)
                    }
                } else {
                    match imported.delta.cmp(&0) {
                        std::cmp::Ordering::Equal => imported.entry_count,
                        std::cmp::Ordering::Greater => OldMachineTerm::add(
                            imported.entry_count,
                            OldMachineTerm::constant(imported.delta.unsigned_abs()),
                        ),
                        std::cmp::Ordering::Less => OldMachineTerm::subtract(
                            imported.entry_count,
                            OldMachineTerm::constant(imported.delta.unsigned_abs()),
                        ),
                    }
                }
            };
            counts.push(count);
        }
        Ok(counts)
    }

    /// A standalone helper's typed lock returns a fresh authority-bearing
    /// control. Its contained authority enters this proof as an arbitrary
    /// existing population: a fresh total, bounded below only by the members
    /// already owned here, with no creator right. Each population may enter
    /// once per proof, so a later acquisition cannot reuse an earlier total.
    pub(crate) fn import_acquired_control_authorities(
        &self,
        instance: &super::super::ResourceInstance,
        definition: &super::super::CompositeResourceDefinition,
        assumptions: &PureFactContext,
        acquired_from: Option<crate::kernel::program_point::ProgramPointId>,
    ) -> Result<Self, String> {
        if !definition.contains().iter().any(|spec| {
            matches!(
                spec.term(),
                super::super::ResourceTerm::PopulationAuthority { .. }
            )
        }) {
            return Ok(self.clone());
        }
        let evaluation =
            super::super::functions::instance_body_evaluation(self, instance, definition)?;
        let mut next = self.clone();
        let mut budget = ExecutionBudget::beside_live_state();
        for spec in definition.contains() {
            if !matches!(
                spec.term(),
                super::super::ResourceTerm::PopulationAuthority { .. }
            ) {
                continue;
            }
            let authority = super::super::functions::evaluate_population_authority_candidate(
                &evaluation,
                &evaluation,
                spec,
                assumptions,
                &mut budget,
            )
            .map_err(|_| "acquired control authority evaluation exceeded its budget")?
            .map_err(|error| {
                format!(
                    "could not evaluate the acquired control authority: {}",
                    crate::kernel::api::describe_certification_runtime_error(&error)
                )
            })?;
            let Resource::PopulationAuthority(description) = authority.resource() else {
                return Err("the acquired control authority is not a population authority".into());
            };
            let events = next
                .population_effects
                .creation
                .as_ref()
                .ok_or("acquired control authority requires the creation ledger")?;
            if events.recognizes_population_authority(description) {
                return Err(format!(
                    "this proof already holds a total for {}(...); acquire its control at most once",
                    description.family()
                ));
            }
            let member = ResourceFact::own(Resource::Composite {
                name: description.family().to_owned(),
                arguments: description.arguments().to_vec().into(),
            });
            let owned = next
                .resources
                .exact_resource_facts(member.resource())
                .into_iter()
                .filter_map(|fact| fact.owned_quantity())
                .sum::<u32>();
            let events = events
                .import_acquired_control_population(description, owned, acquired_from)
                .map_err(|refusal| format!("acquired control authority refused: {refusal}"))?;
            Arc::make_mut(&mut next.population_effects).creation = Some(events);
        }
        Ok(next)
    }

    /// A standalone helper assumes a folded control from its caller. Only the
    /// checked body of that exact owned wrapper may seed its opaque population
    /// inputs; no direct authority or creator right is manufactured here.
    pub(crate) fn import_opaque_control_wrapper(
        &self,
        selected: &ResourceFact,
        definition: &super::super::CompositeResourceDefinition,
        assumptions: &PureFactContext,
        wildcard_members: &std::collections::BTreeMap<
            super::super::ResourceDescription,
            Vec<ResourceFact>,
        >,
    ) -> Result<Self, String> {
        let events = self
            .population_effects
            .creation
            .as_ref()
            .ok_or("opaque control requires the creation ledger")?
            .import_checked_control_wrapper_with_members(
                self,
                selected,
                definition,
                assumptions,
                wildcard_members,
            )?;
        let mut next = self.clone();
        Arc::make_mut(&mut next.population_effects).creation = Some(events);
        Ok(next)
    }

    /// Authenticate an exact authority-bearing wrapper. An explicit counter
    /// equality supplies its owned cell load as the entry count witness; a
    /// generic wrapper leaves the count arbitrary for the ledger to name.
    pub(in crate::kernel) fn checked_authority_wrapper_import_components(
        &self,
        selected: &ResourceFact,
        definition: &super::super::CompositeResourceDefinition,
        assumptions: &PureFactContext,
    ) -> Result<Vec<(ResourceDescription, Option<OldMachineTerm>)>, String> {
        if !self.resources.contains_exact_representation(selected) {
            return Err("Requires the declared owned control resource".into());
        }
        let (children, descriptions) =
            self.authority_wrapper_candidates(selected, definition, assumptions, true)?;
        let mut components = Vec::with_capacity(descriptions.len());
        for description in &descriptions {
            let Some(
                [crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(anchor_value))],
            ) = (description.arguments()).fixed_values::<1>()
            else {
                return Err("control authority needs one pointer anchor".into());
            };
            let anchor = anchor_value.address().clone();
            let ResourceFact::Own(Resource::Composite { arguments, .. }, _) = selected else {
                return Err("Requires owns control resource".into());
            };
            if arguments != description.arguments() || definition.parameters().len() != 1 {
                return Err("control and authority need the same pointer argument".into());
            }
            let parameter = definition.parameters()[0].name();
            let memory_cells = children
                .iter()
                .filter_map(ResourceFact::memory_own_range)
                .collect::<Vec<_>>();
            let allocations = children
                .iter()
                .filter_map(ResourceFact::allocation)
                .collect::<Vec<_>>();
            let owns_counter = memory_cells.iter().any(|range| {
                range.base() == &anchor
                    && range.constant_start() == Some(0)
                    && range.constant_end().is_some_and(|end| {
                        end.checked_mul(range.element_width())
                            .is_some_and(|bytes| bytes >= 4)
                    })
            });
            if children.len() != descriptions.len() + memory_cells.len() + allocations.len()
                || allocations.len() > 1
                || allocations.iter().any(|(base, _)| *base != &anchor)
            {
                return Err("control must own exact memory, allocation, and authority".into());
            }
            let is_parameter = |expression: &SpecExpression| matches!(expression, SpecExpression::ProgramExpression(ProgramExpression::Variable(name)) if name.is_named(parameter));
            let is_counter_load = |expression: &SpecExpression| {
                let SpecExpression::MemoryLoad {
                    point: SpecPoint::Current,
                    pointer,
                    value_type: ProgramType::Int32,
                    exact: false,
                } = expression
                else {
                    return false;
                };
                match pointer.as_ref() {
                    // The first int32 field of a struct (for example `obj->refs`)
                    // lowers to a load at the struct base, not an array offset.
                    direct if is_parameter(direct) => true,
                    SpecExpression::PointerOffset {
                        pointer,
                        elements,
                        byte_width: 4,
                    } => {
                        is_parameter(pointer)
                            && matches!(elements.as_ref(), SpecExpression::Value(ProgramValue::Int32(zero)) if zero.as_const() == Some(0))
                    }
                    _ => false,
                }
            };
            let is_population_count = |expression: &SpecExpression| {
                matches!(expression, SpecExpression::CountedResourceCount { name, arguments }
                if name == description.family()
                    && arguments.len() == description.population_arity().unwrap_or(1)
                    && arguments.first().is_some_and(|arg| arg.as_ref().is_some_and(is_parameter))
                    && arguments[1..].iter().all(Option::is_none))
            };
            let exact_count_fact = definition.facts().iter().any(|fact| {
                matches!(fact, SpecProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            right,
        } if (is_counter_load(left) && is_population_count(right))
            || (is_population_count(left) && is_counter_load(right)))
            });
            if !exact_count_fact {
                components.push((description.clone(), None));
                continue;
            }
            if !owns_counter {
                return Err("coupled control must own its exact counter cell".into());
            }
            components.push((
                description.clone(),
                Some(crate::kernel::OldMachineTerm::read_named(
                    ProgramPoint::unplaced(&(intern_memory_ref(&self.memory))),
                    anchor.clone(),
                    LoadKind::Int32,
                )),
            ));
        }
        Ok(components)
    }

    fn authority_wrapper_candidates(
        &self,
        selected: &ResourceFact,
        definition: &super::super::CompositeResourceDefinition,
        assumptions: &PureFactContext,
        require_folded: bool,
    ) -> Result<(Vec<ResourceFact>, Vec<ResourceDescription>), String> {
        // A control with model fields is held as an instance. Its fields never
        // decide which resources its body owns: only the owned clauses below
        // are evaluated, over its parameters, and a clause that needed a
        // field value would fail to evaluate rather than be admitted.
        let (name, arguments, quantity, has_fields) = match selected {
            ResourceFact::Own(Resource::Composite { name, arguments }, quantity) => {
                (name.as_str(), arguments, quantity, false)
            }
            ResourceFact::Own(Resource::Instance(instance), quantity) => (
                instance.name(),
                instance.arguments(),
                quantity,
                !instance.schema().fields().is_empty(),
            ),
            _ => return Err("Requires owns control resource".into()),
        };
        if name != definition.name()
            || quantity.as_const() != Some(1)
            || (require_folded && !self.resources.satisfies_fact(selected, assumptions))
            || definition.parameters().len() != arguments.len()
            || (!has_fields
                && definition
                    .instance_schema
                    .as_ref()
                    .is_some_and(|schema| !schema.fields().is_empty()))
            || definition.matched.is_some()
            || !definition.witnesses.is_empty()
            || definition.condition.is_some()
            || !definition.children.is_empty()
            || !definition.resource_parameters.is_empty()
        {
            return Err("Requires one folded authority control resource".into());
        }
        let mut evaluation = ExecutionState::new().with_memory(self.memory.clone());
        evaluation.population_effects = self.population_effects.clone();
        for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
            let value = argument
                .as_program_value()
                .ok_or("control resource needs concrete arguments")?;
            if parameter.program_type() != value.program_type() {
                return Err("control resource argument has the wrong type".into());
            }
            evaluation.locals.set_typed(
                parameter.binding_name().clone(),
                value.clone(),
                parameter.program_type(),
            );
        }
        let mut children = Vec::with_capacity(definition.contains().len());
        let mut authorities = Vec::new();
        let mut seen_authorities = std::collections::BTreeSet::new();
        let mut budget = ExecutionBudget::beside_live_state();
        for spec in definition.contains() {
            if spec.access() != super::super::ResourceAccessMode::Own
                || spec.quantity() != &super::super::ResourceQuantity::One
                || spec.guard().is_some()
                || !spec.resource_arguments().is_empty()
            {
                return Err("control body requires exact owned resources".into());
            }
            let child = match spec.term() {
                super::super::ResourceTerm::PopulationAuthority { .. } => {
                    if authorities.len() == 2 {
                        return Err(
                            "control body currently supports at most two authorities".into()
                        );
                    }
                    super::super::functions::evaluate_population_authority_candidate(
                        &evaluation,
                        &evaluation,
                        spec,
                        assumptions,
                        &mut budget,
                    )
                    .map_err(|error| format!("control authority evaluation failed: {error}"))?
                    .map_err(|error| format!("control authority evaluation failed: {error}"))?
                }
                super::super::ResourceTerm::Memory(_) => {
                    // The held control's body, as its fold established it
                    // (`assume_entry_clause_spans`).
                    super::super::functions::evaluate_function_resource_spec(
                        &evaluation,
                        spec,
                        &assumptions.clone().assume_entry_clause_spans(),
                        &mut budget,
                    )
                    .map_err(|error| format!("control memory evaluation failed: {error}"))?
                    .map_err(|error| format!("control memory evaluation failed: {error}"))?
                }
                super::super::ResourceTerm::Token { name, .. }
                    if name == ResourceFact::ALLOCATION_RESOURCE_NAME =>
                {
                    // The held control's body, as its fold established it
                    // (`assume_entry_clause_spans`).
                    super::super::functions::evaluate_function_resource_spec(
                        &evaluation,
                        spec,
                        &assumptions.clone().assume_entry_clause_spans(),
                        &mut budget,
                    )
                    .map_err(|error| format!("control allocation evaluation failed: {error}"))?
                    .map_err(|error| format!("control allocation evaluation failed: {error}"))?
                }
                _ => {
                    return Err(
                        "control body supports owned memory, allocation, and authorities".into(),
                    );
                }
            };
            if let Resource::PopulationAuthority(description) = child.resource() {
                if !seen_authorities.insert(description.clone()) {
                    return Err("control body repeats a population authority".into());
                }
                if authorities
                    .first()
                    .is_some_and(|first: &ResourceDescription| {
                        first.arguments() != description.arguments()
                    })
                {
                    return Err("control authorities need the same pointer anchor".into());
                }
                authorities.push(description.clone());
            }
            children.push(child);
        }
        if !require_folded
            && let Some(missing) = children
                .iter()
                .find(|child| !self.resources.satisfies_fact(child, assumptions))
        {
            let kind = if missing.allocation().is_some() {
                "allocation"
            } else {
                match missing.resource() {
                    Resource::Memory(_) => "memory",
                    Resource::PopulationAuthority(_) => "population authority",
                    _ => "resource",
                }
            };
            let detail = missing.allocation().map(|(pointer, bytes)| {
                let detail = format!("anchor={pointer:?}, bytes={bytes:?}");
                detail.chars().take(256).collect::<String>()
            });
            return Err(match detail {
                Some(detail) => {
                    format!("Requires the owned authority control body: missing {kind} ({detail})")
                }
                None => format!("Requires the owned authority control body: missing {kind}"),
            });
        }
        if authorities.is_empty() {
            return Err("control body requires population authority".into());
        }
        Ok((children, authorities))
    }

    #[cfg(test)]
    pub(in crate::kernel) fn population_storage_created_here(&self, pointer: &Address) -> bool {
        matches!(pointer.offset.view(), OffsetView::Constant(0))
            && (matches!(&pointer.base, AddressBase::Heap(_))
                && self.memory.live_heap_block_size(pointer).is_some()
                || pointer.base.is_local_block() && self.memory.has_block(&pointer.base))
            && self
                .population_effects
                .creation
                .as_ref()
                .is_some_and(|events| events.created_here(&pointer.base))
    }

    /// The only state transition that creates or retires a population
    /// authority resource. The event ledger owns the abstract population
    /// identity and its zero-count retirement check; the resource algebra
    /// checks exclusive possession of the visible fact.
    pub(crate) fn checked_population_authority_exchange(
        &self,
        selected: &ResourceFact,
        establish: bool,
        assumptions: &PureFactContext,
    ) -> Result<(ExecutionState, CheckedPopulationAuthorityExchange), String> {
        if self
            .population_effects
            .predicate_count_permissions
            .is_some()
        {
            return Err("predicate count states cannot change authority".into());
        }
        let ResourceFact::Own(Resource::PopulationAuthority(description), quantity) = selected
        else {
            return Err("Requires owns authority(R(p))".into());
        };
        if quantity.as_const() != Some(1) {
            return Err("Requires one authority(R(p))".into());
        }
        let Some([crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(pointer))]) =
            (description.arguments()).fixed_values::<1>()
        else {
            return Err("authority requires one pointer anchor".into());
        };
        let anchor = pointer.address();
        let events = self
            .population_effects
            .creation
            .as_ref()
            .ok_or("the state has no creation history")?;
        let imported_retirement = !establish
            && is_external_population_anchor(anchor)
            && self
                .population_effects
                .creation
                .as_ref()
                .is_some_and(|events| events.recognizes_imported_population(description));
        if imported_retirement {
            self.population_effects.creation.as_ref().expect("imported population")
                .check_imported_retirement(description, assumptions)
                .map_err(|_| format!("Requires count({}(...)) == 0 and no outstanding member custody before authority retirement", description.family()))?;
        }
        if !imported_retirement
            && (!matches!(anchor.offset.view(), OffsetView::Constant(0))
                || !(matches!(&anchor.base, AddressBase::Heap(_))
                    && self.memory.live_heap_block_size(anchor).is_some()
                    || anchor.base.is_local_block() && self.memory.has_block(&anchor.base)))
        {
            return Err("Requires live base storage for authority(R(p))".into());
        }
        let mut next = self.clone();
        let evidence = if establish {
            let (history, evidence) = events
                .checked_establish(&anchor.base, description)
                .map_err(|refusal| format!("authority establishment refused: {refusal}"))?;
            let resources = self
                .resources
                .clone()
                .try_compose_with_fact(selected.clone(), assumptions)
                .map_err(|error| format!("authority ownership refused: {error}"))?;
            next.resources = resources;
            Arc::make_mut(&mut next.population_effects).creation = Some(history);
            evidence
        } else {
            let resources = self
                .resources
                .clone()
                .without_fact_incrementally(selected, assumptions)
                .ok_or("Requires owns authority(R(p))")?;
            let (history, evidence) = if imported_retirement {
                events.checked_retire_imported(description, assumptions)
            } else {
                events.checked_retire(&anchor.base, description)
            }
            .map_err(|refusal| format!("authority retirement refused: {refusal}"))?;
            next.resources = resources;
            Arc::make_mut(&mut next.population_effects).creation = Some(history);
            evidence
        };
        Ok((next, evidence))
    }

    /// Exchange one member and its private owned-memory body while the
    /// matching authority is owned. The resource and population ledgers
    /// advance together.
    pub(crate) fn checked_population_member_exchange(
        &self,
        selected: &ResourceFact,
        produce: bool,
        definition: &super::super::CompositeResourceDefinition,
        assumptions: &PureFactContext,
    ) -> Result<(ExecutionState, CheckedPopulationMemberExchange), String> {
        if self
            .population_effects
            .predicate_count_permissions
            .is_some()
        {
            return Err("predicate count states cannot change membership".into());
        }
        let ResourceFact::Own(Resource::Composite { name, arguments }, quantity) = selected else {
            return Err("Requires owns R(p)".into());
        };
        if let Some(value) = quantity.as_const()
            && (value as i32) < 0
        {
            return Err(format!(
                "Requires 0 <= {} (resource quantity)",
                value as i32
            ));
        }
        let batch = quantity.as_const() != Some(1);
        if definition.name != *name
            || !definition.resource_parameters.is_empty()
            || definition.matched.is_some()
            || !definition.witnesses.is_empty()
            || definition.condition.is_some()
            || definition.facts_claim_liveness
            || !definition.children.is_empty()
            || definition
                .instance_schema
                .as_ref()
                .is_some_and(|schema| !schema.fields().is_empty())
            || definition.contains().iter().any(|spec| {
                !matches!(
                    spec.term(),
                    super::super::ResourceTerm::Memory(_)
                        | super::super::ResourceTerm::Token { .. }
                        | super::super::ResourceTerm::Composite { .. }
                ) || spec.access() != super::super::ResourceAccessMode::Own
                    || spec.quantity() != &super::super::ResourceQuantity::One
                    || spec.guard().is_some()
                    || !spec.resource_arguments().is_empty()
            })
        {
            return Err("member exchange requires a field-free private body of owned memory or declared resources".into());
        }
        let description = super::super::ResourceDescription::new(
            name.clone(),
            arguments.clone(),
            super::super::ResourceFieldSchema::new(vec![]).expect("empty resource schema is valid"),
        );
        let Some(crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(pointer))) =
            description.arguments().first()
        else {
            return Err("Requires an exact pointer-anchored authorized resource R(p)".into());
        };
        let anchor = pointer.address();
        let imported_member_exchange =
            self.population_effects
                .creation
                .as_ref()
                .is_some_and(|events| {
                    if produce {
                        events.recognizes_imported_population(&description)
                    } else {
                        events.owns_imported_population_member(&description)
                    }
                });
        // The opaque proof receives the body only through its checked
        // contract: on birth the declared memory is consumed below, and on
        // death the imported member is consumed below. The concrete caller
        // still checks the live anchor and transfers those exact resources.
        // An imported population has no local storage to check; spending a
        // member this proof does not hold is a missing member, not storage.
        if !imported_member_exchange
            && !produce
            && self
                .population_effects
                .creation
                .as_ref()
                .is_some_and(|events| events.recognizes_imported_population(&description))
        {
            return Err(format!("Requires owns {name}(p)"));
        }
        if !imported_member_exchange
            && (!matches!(anchor.offset.view(), OffsetView::Constant(0))
                || !(matches!(&anchor.base, AddressBase::Heap(_))
                    && self.memory.live_heap_block_size(anchor).is_some()
                    || anchor.base.is_local_block() && self.memory.has_block(&anchor.base)))
        {
            return Err("Requires live base storage for R(p)".into());
        }
        let governing = self
            .population_effects
            .creation
            .as_ref()
            .and_then(|events| events.governing_authority(&description))
            .ok_or_else(|| {
                format!(
                    "Requires owns authority({name}(anchor, {}))",
                    std::iter::repeat_n("_", arguments.len().saturating_sub(1))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            })?;
        let authority = ResourceFact::own(Resource::PopulationAuthority(governing.clone()));
        if !self.resources.satisfies_fact(&authority, assumptions) {
            return Err(format!("Requires owns authority({name}(p))"));
        }
        if self.population_body_is_open(name, arguments) {
            return Err("close the member's private body before changing its population".into());
        }
        let events = self
            .population_effects
            .creation
            .as_ref()
            .ok_or("the state has no creation history")?;
        if batch && (!definition.contains().is_empty() || !definition.facts().is_empty()) {
            return Err("a quantified member needs an empty private body".into());
        }
        let body = if definition.contains().is_empty() {
            Vec::new()
        } else {
            let singleton = ResourceContext::new_with_equalities(assumptions)
                .unchecked_with_fact(selected.clone());
            let expanded = crate::kernel::functions::expand_composite_resource_fact(
                &singleton,
                selected,
                std::slice::from_ref(definition),
                &self.program_point(),
                assumptions,
            )
            .ok_or("cannot instantiate the member's private body")?;
            expanded.facts().to_vec()
        };
        for child in &body {
            let Some(range) = child.memory_own_range() else {
                if let ResourceFact::Own(
                    Resource::Token { .. } | Resource::Composite { .. },
                    quantity,
                ) = child
                    && quantity.as_const() == Some(1)
                {
                    // Transfer the folded child; do not expose its contents or
                    // change its population membership.
                    continue;
                }
                return Err(
                    "member body must contain owned memory or owned declared resources".into(),
                );
            };
            let (Some(start), Some(end)) = (range.constant_start(), range.constant_end()) else {
                return Err("member private memory needs concrete bounds".into());
            };
            let (start, end) = (start as i32, end as i32);
            let bytes = end
                .checked_sub(start)
                .filter(|length| *length > 0)
                .and_then(|length| length.checked_mul(range.element_width() as i32))
                .and_then(|bytes| u32::try_from(bytes).ok())
                .ok_or("member private memory needs a positive bounded range")?;
            let base = range.start_pointer();
            // Birth checks the supplied body's storage. On death the owned
            // member is the evidence: consuming it below returns that same
            // body. Do not rediscover its introduction premises from the
            // current ambient loadability facts.
            if produce
                && !imported_member_exchange
                && !self.memory.access_in_bounds(&base, bytes)
                && !assumptions.proves_memory_loadable_for_memory_resolution(
                    &self.memory,
                    &self.memory_point(),
                    &base,
                    &OldMachineTerm::constant(bytes),
                )
            {
                return Err("member private memory exceeds live storage".into());
            }
            if self
                .borrow_ledger()
                .is_some_and(|ledger| !ledger.rewrite_separates_from_borrows(range, assumptions))
            {
                return Err("member private memory requires separation from active borrows".into());
            }
        }
        if produce && !definition.facts().is_empty() {
            let instantiated = crate::kernel::functions::instantiate_private_member_body_facts(
                selected,
                definition,
                self,
                assumptions,
            )
            .ok_or("Requires ownership of every cell read by member body facts")?;
            for (index, fact) in instantiated.declared {
                if !assumptions.proves_exact(&fact) {
                    return Err(format!("Requires member body fact #{index}"));
                }
            }
        }
        let resources = if produce {
            let mut resources = self.resources.clone();
            for child in &body {
                resources = resources
                    .without_fact_incrementally(child, assumptions)
                    .ok_or_else(|| format!("Requires the private body of {name}(p)"))?;
            }
            resources
                .try_compose_with_fact(selected.clone(), assumptions)
                .map_err(|error| format!("member ownership refused: {error}"))?
        } else {
            let resources = self
                .resources
                .clone()
                .without_fact_incrementally(selected, assumptions)
                .ok_or_else(|| format!("Requires owns {name}(p)"))?;
            resources
                .install_established_partition(body.iter().cloned(), assumptions)
                .map(|(context, _)| context)
                .map_err(|error| format!("member body ownership refused: {error}"))?
        };
        let exchange = if definition.has_fixed_exclusive_memory() {
            events.checked_exclusive_member_exchange_quantity(
                &anchor.base,
                &description,
                produce,
                quantity.old_form(),
                assumptions,
            )
        } else {
            events.checked_member_exchange_quantity(
                &anchor.base,
                &description,
                produce,
                quantity.old_form(),
                assumptions,
            )
        };
        let (history, evidence) = exchange
            .map_err(|error| {
                if produce && governing.population_arity().is_some()
                    && events.observe_symbolic(&governing).is_some()
                    && matches!(error, super::super::population_authority::storage_creation::CreationRefusal::InvalidQuantity)
                {
                    format!("Requires defined(count({name}({}, {})) + 1)", definition.parameters().first().map_or("anchor", |parameter| parameter.name()),
                        std::iter::repeat_n("_", arguments.len() - 1).collect::<Vec<_>>().join(", "))
                } else { format!("member change refused: {error}") }
            })?;
        let mut next = self.clone();
        next.resources = resources;
        Arc::make_mut(&mut next.population_effects).creation = Some(history);
        Ok((next, evidence))
    }

    /// Named ownership remains in the resource context; the authority ledger
    /// records only its birth or consumption. Opening a body is a different
    /// operation and does not use this lifecycle exchange.
    pub(in crate::kernel) fn record_instance_population_exchange(
        &mut self,
        before: &ExecutionState,
        instance: &super::super::ResourceInstance,
        produce: bool,
        assumptions: &PureFactContext,
    ) -> Result<(), String> {
        if before
            .population_effects
            .predicate_count_permissions
            .is_some()
        {
            return Err("predicate count states cannot change named membership".into());
        }
        let Some(events) = &before.population_effects.creation else {
            return Ok(());
        };
        let description = super::super::ResourceDescription::from_instance(instance);
        let history = if events.tracks_population(&description) {
            let governing = events
                .governing_authority(&description)
                .ok_or("Requires a matching population authority")?;
            let authority = ResourceFact::own(Resource::PopulationAuthority(governing.clone()));
            if !before.resources.satisfies_fact(&authority, assumptions) {
                return Err(format!("Requires owns authority({}(...))", instance.name()));
            }
            let reference = super::super::ResourceReference::from_instance(instance);
            if events.recognizes_imported_population(&description) {
                let owned = ResourceFact::own(Resource::Instance(instance.clone()));
                if !produce && !before.resources.satisfies_fact(&owned, assumptions) {
                    return Err("Requires owning the exact named member before consumption".into());
                }
                events
                    .checked_imported_instance_exchange(instance, produce, assumptions)
                    .map_err(|refusal| format!("named member change refused: {refusal}"))?
            } else {
                events
                    .checked_instance_exchange(&reference, produce)
                    .map_err(|refusal| format!("named member change refused: {refusal}"))?
            }
        } else if produce {
            let Some(crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(pointer))) =
                description.arguments().first()
            else {
                return Ok(());
            };
            events.member_created(&pointer.address().base, description.family())
        } else {
            return Ok(());
        };
        Arc::make_mut(&mut self.population_effects).creation = Some(history);
        Ok(())
    }

    pub(in crate::kernel) fn record_population_storage_creation(&mut self, block: AddressBase) {
        if let Some(events) = &self.population_effects.creation {
            Arc::make_mut(&mut self.population_effects).creation = Some(events.created(block));
        }
    }

    pub(in crate::kernel) fn record_pending_population_storage_creation(
        &mut self,
        block: AddressBase,
    ) {
        if let Some(events) = &self.population_effects.creation {
            Arc::make_mut(&mut self.population_effects).creation =
                Some(events.pending_creation(block));
        }
    }

    pub(in crate::kernel) fn resolve_pending_population_storage_creation(
        &mut self,
        pending_block: &AddressBase,
        live_block: Option<AddressBase>,
    ) {
        if let Some(events) = &self.population_effects.creation {
            let next = events.resolve_pending(pending_block, live_block);
            if &next != events {
                Arc::make_mut(&mut self.population_effects).creation = Some(next);
            }
        }
    }

    pub(in crate::kernel) fn retire_population_storage(
        &mut self,
        block: &AddressBase,
    ) -> Result<(), RuntimeError> {
        if let Some(events) = &self.population_effects.creation {
            let next = events.retired(block).map_err(|refusal| {
                RuntimeError::FunctionContract(format!(
                    "population authority prevents storage retirement: {refusal}"
                ))
            })?;
            Arc::make_mut(&mut self.population_effects).creation = Some(next);
        }
        Ok(())
    }

    /// Retire a returning frame's blocks while its own creation environment
    /// still owns them. The caller environment is restored only afterward.
    pub(in crate::kernel) fn retired_population_creation_for_blocks(
        &self,
        blocks: &[AddressBase],
    ) -> Result<
        Option<super::super::population_authority::storage_creation::CreationEvents>,
        RuntimeError,
    > {
        let Some(mut events) = self.population_effects.creation.clone() else {
            return Ok(None);
        };
        for block in blocks {
            events = events.retired(block).map_err(|refusal| {
                RuntimeError::FunctionContract(format!(
                    "population authority prevents storage retirement: {refusal}"
                ))
            })?;
        }
        Ok(Some(events))
    }

    pub(in crate::kernel) fn population_storage_retirement_refusal(
        &self,
        block: &AddressBase,
    ) -> Option<RuntimeError> {
        self.population_effects
            .creation
            .as_ref()
            .and_then(|events| events.retirement_refusal(block))
            .map(|refusal| {
                RuntimeError::FunctionContract(format!(
                    "population authority prevents storage retirement: {refusal}"
                ))
            })
    }

    /// Recover caller environment identity while retaining any creation
    /// events produced by a body that actually executed.
    pub(in crate::kernel) fn restore_population_creation_after_call(
        &mut self,
        caller: Option<&super::super::population_authority::storage_creation::CreationEvents>,
        callee: Option<&super::super::population_authority::storage_creation::CreationEvents>,
    ) {
        let next = match (caller, callee) {
            (Some(caller), Some(callee)) => Some(callee.return_to(caller)),
            (None, None) => None,
            // A missing ledger cannot justify an origin in either direction.
            _ => None,
        };
        if self.population_effects.creation != next {
            Arc::make_mut(&mut self.population_effects).creation = next;
        }
    }

    pub(in crate::kernel) fn with_next_local_frame(mut self, next: u64) -> Self {
        self.next_local_frame = next;
        self
    }

    pub(in crate::kernel) fn next_local_lifetime(&self) -> u64 {
        self.next_local_lifetime
    }

    pub(crate) fn with_next_local_lifetime(mut self, next: u64) -> Self {
        self.next_local_lifetime = next;
        self
    }

    pub(in crate::kernel) fn enclosing_frame_holds_locals(&self) -> bool {
        self.enclosing_frame_holds_locals
    }

    pub(in crate::kernel) fn with_enclosing_frame_holds_locals(mut self, nested: bool) -> Self {
        self.enclosing_frame_holds_locals = nested;
        self
    }

    #[cfg(test)]
    pub(crate) fn shares_nonlocal_storage_with(&self, other: &Self) -> bool {
        std::sync::Arc::ptr_eq(&self.memory.blocks, &other.memory.blocks)
            && std::sync::Arc::ptr_eq(&self.memory.cells, &other.memory.cells)
            && std::sync::Arc::ptr_eq(&self.memory.union_cells, &other.memory.union_cells)
            && std::sync::Arc::ptr_eq(&self.memory.heap, &other.memory.heap)
            && self.resources.shares_storage_with(&other.resources)
            && match (&self.borrow_ledger, &other.borrow_ledger) {
                (None, None) => true,
                (Some(left), Some(right)) => left.shares_storage_with(right),
                _ => false,
            }
            && self.borrow_participant == other.borrow_participant
            && self.borrow_bindings == other.borrow_bindings
            && self
                .observed_population_families
                .shares_storage_with(&other.observed_population_families)
    }

    pub fn with_local(mut self, name: impl Into<BindingName>, value: ProgramValue) -> Self {
        self.locals.set(name, value);
        self
    }

    /// Bind an existing producer for proof-side expression lowering through
    /// the same local type/qualifier policy as `with_local`.
    pub(crate) fn with_retained_local(
        mut self,
        name: impl Into<BindingName>,
        value: ExecutionValue,
    ) -> Self {
        if let ExecutionValue::Native(value) = value {
            return self.with_local(name, value);
        }
        let program_type = value.program_type();
        self.locals.set_retained_typed_with_all_qualifiers(
            name,
            value,
            program_type,
            false,
            false,
            false,
            false,
        );
        self
    }

    pub fn with_memory(mut self, memory: SymbolicMemory) -> Self {
        self.set_memory(memory);
        self
    }

    /// Install memory built from a shared base. Register its identity by
    /// changed paths before resource invalidation or the point link looks it up.
    pub(in crate::kernel) fn with_memory_relative_to(
        self,
        memory: SymbolicMemory,
        base: &SymbolicMemory,
    ) -> Self {
        super::intern_memory_with(std::borrow::Cow::Borrowed(&memory), Some(base), None);
        self.with_memory(memory)
    }

    /// Replace the memory state after proof-only cell naming.
    ///
    /// Materializing a canonical load does not write program memory or
    /// invalidate an existing view. The ordinary [`Self::with_memory`] path
    /// deliberately invalidates memory-dependent projections for evaluator
    /// writes, but using it for this proof representation step would discard
    /// unrelated resource views and make a resource rewrite appear to change
    /// more authority than its definition exchanges.
    pub(crate) fn with_materialized_memory(mut self, memory: SymbolicMemory) -> Self {
        self.memory = memory;
        self
    }

    /// Install a proof-only view at the current point. Settle genuine source
    /// steps first. Keep the path's versions available through a certified
    /// naming suffix without turning those cache entries into execution steps.
    pub(crate) fn with_materialized_memory_at_current_point(
        mut self,
        mut memory: SymbolicMemory,
    ) -> Self {
        let source = super::intern_memory_ref(&self.memory);
        let view = super::intern_memory_ref(&memory);
        let verified = super::program_point::StepLog::materializes_from(
            &source,
            self.memory.pending_steps.as_ref(),
            &view,
            memory.pending_steps.as_ref(),
        );
        assert!(
            self.memory.pending_steps.is_none(),
            "a proof-only view is installed at a settled point"
        );
        self.point = self.point.with_materialized_view(&source, &view, verified);
        memory.pending_steps = None;
        self.with_materialized_memory(memory)
    }

    /// Start the path of a standalone function proof after preparing its
    /// storage. Contract-provided cells belong to this entry point.
    pub(crate) fn begin_function_entry_memory(mut self) -> Self {
        self.memory.pending_steps = None;
        let memory = super::intern_memory_ref(&self.memory);
        self.point = super::program_point::PathLink::function_entry(memory);
        self
    }

    /// Install a provisional or finished memory view during function entry
    /// setup. The setup log describes initial contents and does not record
    /// executed statements. Keep the ordinary resource invalidation checks.
    pub(crate) fn with_function_entry_memory(mut self, memory: SymbolicMemory) -> Self {
        self.replace_memory(memory, false);
        self.memory.pending_steps = None;
        self.point = self
            .point
            .with_entry_view(&super::intern_memory_ref(&self.memory));
        self
    }

    /// Replace memory through the single checked-state transition hook.
    /// Keeping this beside `with_memory` prevents evaluator paths that already
    /// own a mutable state from bypassing resource-observation invalidation.
    /// Whether `self == other`, for two states whose memories were each
    /// derived from `base` by persistent updates, as the abstractions of two
    /// arms are derived from the memory at their split. The memories are
    /// compared by what each changed from `base`
    /// ([`SymbolicMemory::eq_relative_to`]), so the cost is the arms' changes; the
    /// answer is exact whatever the memories share.
    pub(crate) fn eq_with_memories_from(&self, other: &Self, base: &SymbolicMemory) -> bool {
        if !self.memory.eq_relative_to(&other.memory, base) {
            return false;
        }
        // The memories are equal, so the rest is compared with one memory
        // standing on both sides, where it is equal by identity.
        let mut other = other.clone();
        other.memory = self.memory.clone();
        *self == other
    }

    pub(crate) fn set_memory(&mut self, memory: SymbolicMemory) {
        self.set_memory_with_checked_stores(memory, false);
    }

    /// [`Self::set_memory`] for the C store path, which has already applied
    /// the iterated-ownership store rule (`plan_iterated_guard_store`) to its
    /// one store. Every other transition keeps the conservative rule.
    pub(crate) fn set_memory_with_checked_stores(
        &mut self,
        memory: SymbolicMemory,
        stores_checked: bool,
    ) {
        self.replace_memory(memory, stores_checked);
        let steps = self.memory.pending_steps.take();
        self.point = self
            .point
            .after(super::intern_memory_ref(&self.memory), steps);
    }

    /// Take `source`'s memory, with [`Self::set_memory`]'s resource
    /// invalidation, and stand where `source` stands: the steps that made
    /// that memory were taken on `source`'s path, so this state's path
    /// continues from there.
    pub(crate) fn set_memory_of(&mut self, source: &Self) {
        self.set_memory_continuing(source, source.memory.clone());
    }

    /// [`Self::set_memory_of`], by value.
    pub(crate) fn with_memory_of(mut self, source: &Self) -> Self {
        self.set_memory_of(source);
        self
    }

    /// Take `memory`, made from `from`'s memory by the steps in its own log,
    /// with [`Self::set_memory`]'s resource invalidation: this state's path
    /// continues from `from`'s point through those steps.
    pub(crate) fn set_memory_continuing(&mut self, from: &Self, memory: SymbolicMemory) {
        let base = from.program_point();
        self.replace_memory(memory, false);
        self.record_memory_continuation(&base);
    }

    /// Resume the caller with the callee's memory and the checked return
    /// partition together. Resource recovery has already constructed the new
    /// frame, so there is no old-frame projection to invalidate here.
    pub(in crate::kernel) fn with_call_return(
        self,
        callee: &Self,
        resources: ResourceContext,
    ) -> Self {
        self.with_memory_and_resources_continuing(callee, callee.memory.clone(), resources)
    }

    /// Continue from the producer's path with the memory and resource
    /// partition it has already prepared for this outcome.
    pub(in crate::kernel) fn with_memory_and_resources_continuing(
        mut self,
        from: &Self,
        memory: SymbolicMemory,
        resources: ResourceContext,
    ) -> Self {
        let base = from.program_point();
        self.memory = memory;
        self.record_memory_continuation(&base);
        self.with_resource_context(resources)
    }

    fn record_memory_continuation(&mut self, base: &super::ProgramPoint) {
        let steps = self.memory.pending_steps.take();
        let shared = super::intern_memory_ref(&self.memory);
        self.point = if steps.is_none() && base.shared_memory() == &shared {
            base.path_link().clone()
        } else {
            base.path_link().after(shared, steps)
        };
    }

    /// [`Self::set_memory_continuing`], by value.
    pub(crate) fn with_memory_continuing(mut self, from: &Self, memory: SymbolicMemory) -> Self {
        self.set_memory_continuing(from, memory);
        self
    }

    /// Replace memory, dropping the resource projections it touches.
    fn replace_memory(&mut self, memory: SymbolicMemory, stores_checked: bool) {
        self.resources = self
            .resources
            .clone()
            .invalidate_memory_support(&self.memory, &memory)
            .invalidate_iterated_facts(&self.memory, &memory, stores_checked);
        self.borrow_bindings = crate::kernel::borrows::BorrowBindings::from_state(
            self.resources.borrow_dependency_state(),
        );
        self.memory = memory;
    }

    /// The point this state stands at on its path.
    pub(crate) fn program_point(&self) -> super::ProgramPoint {
        super::ProgramPoint::of_state(&self.memory, &self.point)
    }

    /// This state's memory as a memory-named point placed where the state
    /// stands: the point a legacy read of this state is named by.
    pub(crate) fn memory_named_point(&self) -> super::ProgramPoint {
        let point = self.program_point();
        super::ProgramPoint::viewing(point.shared_memory(), &point)
    }

    /// A fresh state standing at `point`: its memory and its place on the
    /// path. A state that evaluates something at a point (a resource body,
    /// a callee frame) starts here, so its reads stay on the point's path.
    pub(crate) fn at_point(point: &super::ProgramPoint) -> Self {
        let mut state = Self::new();
        state.memory = point.memory().clone();
        state.point = point.path_link().clone();
        state
    }

    /// A fresh state standing where `state` stands, holding `state`'s own
    /// memory value. A callee frame is the caller's state at the call seen
    /// through the callee's parameter names, so it starts here; it keeps the
    /// caller's memory value, not only equal contents, because a call's
    /// requirements are matched to the memory they were evaluated in by its
    /// storage.
    pub(crate) fn at_state(state: &Self) -> Self {
        let point = state.program_point();
        let mut fresh = Self::new();
        fresh.memory = state.memory.clone();
        fresh.memory.pending_steps = None;
        fresh.point = point.path_link().clone();
        fresh
    }

    /// Where on its path this state stands.
    pub(crate) fn path_link(&self) -> &super::program_point::PathLink {
        &self.point
    }

    /// The point this state's memory is the state at, for a fact that
    /// quotes it: where the state stands. A state with staged steps stands
    /// between points, and no fact quotes its memory.
    pub(crate) fn memory_point(&self) -> super::program_point::PathLink {
        assert!(
            self.memory.pending_steps.is_none(),
            "a fact quotes a state with staged steps before its atomic region completes"
        );
        self.point.clone()
    }

    /// The identity of the point this state stands at, without interning its
    /// memory.
    pub(crate) fn program_point_id(&self) -> Option<super::program_point::ProgramPointId> {
        self.point.id()
    }

    /// Point of an observation in this state: the point it stands at. A
    /// state with staged steps is between points and is never observed.
    pub(crate) fn observation_point_id(&self) -> Option<super::program_point::ProgramPointId> {
        assert!(
            self.memory.pending_steps.is_none(),
            "a state with staged steps is read before its atomic region completes"
        );
        self.program_point_id()
    }

    /// Take `memory` as one step of the atomic region in progress, with
    /// [`Self::set_memory`]'s resource invalidation, without moving to a new
    /// point: the region's one install, the next [`Self::set_memory`] or
    /// [`Self::complete_staged_memory`], takes every staged step at once.
    /// A state with staged steps stands between points; a region writes it
    /// and never reads it.
    pub(crate) fn stage_memory(&mut self, memory: SymbolicMemory) {
        self.replace_memory(memory, false);
    }

    /// This state, continuing `source`'s atomic region in progress: it
    /// stands where `source` stands and takes its memory, staged steps
    /// included, with [`Self::stage_memory`]'s resource invalidation.
    pub(crate) fn with_staged_memory_of(mut self, source: &Self) -> Self {
        self.point = source.point.clone();
        self.stage_memory(source.memory.clone());
        self
    }

    /// [`Self::stage_memory`] without its resource invalidation, for a step
    /// that has already accounted for it, as [`Self::set_memory_directly`].
    pub(crate) fn stage_memory_directly(&mut self, memory: SymbolicMemory) {
        self.memory = memory;
    }

    /// Ends the atomic region in progress: a state with staged memory moves
    /// to the one new point those steps reach. Without staged memory it
    /// stays where it is.
    pub(crate) fn complete_staged_memory(&mut self) {
        let steps = self.memory.pending_steps.take();
        let shared = super::intern_memory_ref(&self.memory);
        if steps.is_none() && self.point.memory() == Some(&shared) {
            return;
        }
        self.point = self.point.after(shared, steps);
    }

    /// Ends the atomic region in progress at a new point, even when it
    /// staged nothing: a contract call's exit, which follows its effect point.
    pub(crate) fn complete_staged_memory_at_new_point(&mut self) {
        let steps = self.memory.pending_steps.take();
        let shared = super::intern_memory_ref(&self.memory);
        self.point = self.point.after(shared, steps);
    }

    /// Moves this loop exit past a record of what the loop's iterations
    /// wrote, at a new point with the same memory.
    pub(in crate::kernel) fn record_loop_iterations(
        &mut self,
        iterations: super::program_point::LoopIterations,
    ) {
        self.complete_staged_memory();
        self.point = self.point.after_loop_iterations(iterations);
    }

    /// Ends a contract call's value effects: the state moves to the call's
    /// effect point (`call(f, j).effect`) with every staged step, even when
    /// it staged none, so each contract call has one.
    pub(crate) fn complete_staged_memory_as_call_effect(&mut self) {
        let steps = self.memory.pending_steps.take();
        let shared = super::intern_memory_ref(&self.memory);
        self.point = self.point.after_call_effect(shared, steps);
    }

    /// The state at the effect point this state's call reached its exit
    /// from: this state's resources, at that point's memory, with `entry`'s
    /// locals when the call's entry is known, since the call has changed no
    /// local there. None when this state is not a contract call's exit.
    pub(crate) fn call_effect_state(&self, entry: Option<&Self>) -> Option<Self> {
        let [effect] = self.point.predecessors() else {
            return None;
        };
        if !effect.is_call_effect() {
            return None;
        }
        let memory = effect.memory()?.memory().clone();
        let mut state = self.clone();
        state.memory = memory;
        state.point = effect.clone();
        if let Some(entry) = entry {
            state.locals = entry.locals.clone();
        }
        Some(state)
    }

    /// Replace memory without the resource invalidation of
    /// [`Self::set_memory`], for a transition that has already accounted for
    /// it. It is still a transition, so the state moves to a new point.
    pub(crate) fn set_memory_directly(&mut self, memory: SymbolicMemory) {
        self.memory = memory;
        let steps = self.memory.pending_steps.take();
        self.point = self
            .point
            .after(super::intern_memory_ref(&self.memory), steps);
    }

    /// Take `before`'s memory and stand where `before` stood, without the
    /// resource invalidation of [`Self::set_memory_of`]: for a state rebuilt
    /// around unchanged memory, or one taking the memory a transition that
    /// already accounted for its resources produced.
    pub(crate) fn keep_memory_of(&mut self, before: &Self) {
        self.memory = before.memory.clone();
        self.point = before.point.clone();
    }

    /// Stand this state at a new point reached from both arms of a join.
    pub(crate) fn join_program_points(
        &mut self,
        left: &Self,
        right: &Self,
        split: &super::program_point::PathLink,
    ) {
        self.point = super::program_point::PathLink::joining(
            left.program_point(),
            right.program_point(),
            split,
            super::intern_memory_ref(&self.memory),
        );
    }

    pub(crate) fn prepare_interface_join_point(
        &mut self,
        arms: [&Self; 2],
        split: &Self,
        other_abstraction: Option<&Self>,
    ) {
        self.memory.pending_steps = None;
        if let Some(other) = other_abstraction {
            self.point = other.point.clone();
        } else {
            self.join_program_points(arms[0], arms[1], split.path_link());
        }
    }

    pub(in crate::kernel) fn has_interface_join_point(
        &self,
        arms: [&Self; 2],
        split: &Self,
    ) -> bool {
        let [left, right] = self.point.predecessors() else {
            return false;
        };
        left.id() == arms[0].program_point().id()
            && right.id() == arms[1].program_point().id()
            && self
                .point
                .split()
                .and_then(super::program_point::PathLink::id)
                == split.program_point_id()
            && self.point.memory().map(super::SharedMemory::arena_id)
                == Some(super::intern_memory_ref(&self.memory).arena_id())
    }

    /// Apply a loop-head local replacement and its normal resource
    /// invalidation. Publish the accumulated effects once at the head.
    pub(in crate::kernel) fn replace_loop_head_local_cell(
        &mut self,
        slot: Address,
        value: ProgramValue,
    ) {
        let memory = self.memory.clone().store(slot, value);
        self.replace_memory(memory, false);
    }

    /// Install the checked arbitrary-iteration memory as one point. Its
    /// abstract local replacements can discard old versions but are not
    /// execution stores supplying new indexed values.
    pub(in crate::kernel) fn set_loop_head_memory(&mut self, memory: SymbolicMemory) {
        self.replace_memory(memory, false);
        let steps = self.memory.pending_steps.take();
        self.point = self
            .point
            .after_loop_head(super::intern_memory_ref(&self.memory), steps);
    }

    /// The loop successor carries only read versions shared by its exits.
    pub(in crate::kernel) fn join_loop_exit_program_points(&mut self, exits: &[&Self]) {
        let points = exits
            .iter()
            .map(|state| state.program_point())
            .collect::<Vec<_>>();
        self.memory.pending_steps = None;
        self.point = super::program_point::PathLink::joining_points(
            &points,
            None,
            super::intern_memory_ref(&self.memory),
        );
    }

    /// Summarize the installed inputs while establishing an execution entry.
    /// Later calls need only the bindings and resources changed from it.
    pub(crate) fn prepare_execution_variable_reservations(&self) {
        crate::kernel::reasoning::execution_state_variable_bound(self);
    }

    pub fn with_resource_context(mut self, resources: ResourceContext) -> Self {
        // ResourceContext owns the canonical persistent dependency root. The
        // ExecutionState field is only a shared mirror, so replacing a context does
        // not scan unrelated resources or active borrows.
        self.borrow_bindings =
            crate::kernel::borrows::BorrowBindings::from_state(resources.borrow_dependency_state());
        self.resources = resources;
        self
    }

    /// Replace resource representation and install checked dependencies for
    /// occurrences created by that rewrite.  The destination occurrences are
    /// supplied by the resource algebra; this method never derives them from
    /// equal facts or from the active ledger.
    pub(crate) fn with_resource_context_and_borrow_dependencies(
        mut self,
        resources: ResourceContext,
        dependencies: impl IntoIterator<
            Item = (
                crate::kernel::primitives::ResourceOccurrenceId,
                crate::kernel::borrows::BorrowBinding,
            ),
        >,
    ) -> Self {
        self = self.with_resource_context(resources);
        for (occurrence, binding) in dependencies {
            self.resources = self
                .resources
                .with_borrow_dependency(occurrence, binding.clone());
        }
        self.borrow_bindings = crate::kernel::borrows::BorrowBindings::from_state(
            self.resources.borrow_dependency_state(),
        );
        self
    }
    pub(crate) fn borrow_ledger(&self) -> Option<&crate::kernel::borrows::BorrowLedger> {
        self.borrow_ledger.as_ref()
    }
    pub(crate) fn with_borrow_ledger(
        mut self,
        ledger: Option<crate::kernel::borrows::BorrowLedger>,
    ) -> Self {
        self.borrow_ledger = ledger;
        self
    }

    pub(crate) fn borrow_participant(&self) -> Option<crate::kernel::borrows::BorrowParticipantId> {
        self.borrow_participant
    }

    pub(crate) fn with_borrow_participant(
        mut self,
        participant: Option<crate::kernel::borrows::BorrowParticipantId>,
    ) -> Self {
        self.borrow_participant = participant;
        self
    }

    pub(crate) fn borrow_bindings(&self) -> &crate::kernel::borrows::BorrowBindings {
        &self.borrow_bindings
    }

    /// The resource-context sidecar is canonical.  The legacy ledger map is
    /// kept as a mechanically synchronized mirror for call planning and must
    /// agree in both directions before a checked resource transition runs.
    pub(crate) fn borrow_bindings_are_consistent(&self) -> bool {
        let resources_state = self.resources.borrow_dependency_state();
        let mirror_state = self.borrow_bindings.state();
        (resources_state.map.is_empty() && mirror_state.map.is_empty())
            || std::sync::Arc::ptr_eq(&resources_state, &mirror_state)
    }

    pub(crate) fn with_borrow_bindings(
        mut self,
        bindings: crate::kernel::borrows::BorrowBindings,
    ) -> Self {
        self.borrow_bindings = bindings;
        self.resources = self
            .resources
            .clone()
            .with_borrow_dependency_state(self.borrow_bindings.state());
        self
    }

    pub(in crate::kernel) fn automatic_storage_borrow_refusal(
        &self,
        block: &AddressBase,
    ) -> Option<RuntimeError> {
        self.borrow_ledger
            .as_ref()?
            .automatic_storage_retirement_refusal(block, self.memory.block_size(block)?)
            .map(|refusal| RuntimeError::BorrowRefusal(Box::new(refusal)))
    }

    pub fn locals(&self) -> &LocalEnvironment {
        &self.locals
    }

    pub(crate) fn local_object_type(&self, name: impl Into<BindingName>) -> Option<ProgramType> {
        self.locals.object_type(name)
    }

    pub(crate) fn global_object_type(&self, name: impl Into<BindingName>) -> Option<ProgramType> {
        let name = name.into();
        self.locals
            .is_global_object(&name)
            .then(|| self.locals.object_type(&name))
            .flatten()
    }

    pub(crate) fn global_array_element_type(
        &self,
        name: impl Into<BindingName>,
    ) -> Option<ProgramType> {
        let name = name.into();
        self.locals
            .is_array_object(&name)
            .then(|| self.locals.object_type(&name))
            .flatten()
    }

    pub fn memory(&self) -> &SymbolicMemory {
        &self.memory
    }

    /// The value one scalar local or parameter holds now, by name: a stored
    /// local's slot cell, or a logical parameter's binding, which no store
    /// can change. Nothing when a stored slot's cell is not known.
    pub(crate) fn scalar_local_value(&self, name: impl Into<BindingName>) -> Option<ProgramValue> {
        let name = name.into();
        match self.locals.binding(&name)? {
            LocalBinding::Object {
                storage_declared: false,
                value,
                slot,
                ..
            } => self
                .memory
                .known_value(slot)
                .or_else(|| Some(value.clone().into_native())),
            LocalBinding::Object { slot, .. } => self.memory.known_value(slot),
            _ => None,
        }
    }

    /// The values held by memory-resident scalar locals at offset zero.
    /// Resolve names through the local-slot index so framed parameter blocks
    /// are exposed with their source name rather than their internal block id.
    pub fn local_cell_values(&self) -> impl Iterator<Item = (&BindingName, ProgramValue)> + '_ {
        // A local's slot is at offset zero of its block, so a run holds one
        // only at the slot spelled that way, looked up rather than visited.
        let run_slots = self.memory.cells.runs().filter_map(|run| {
            let pointer = run.base().with_offset(AddressOffset::constant(0));
            let index = run.live_slot_index(&pointer)?;
            Some((pointer, run.value(index)))
        });
        let mut values = self
            .memory
            .cells
            .concrete()
            .iter()
            .filter(|(pointer, _)| matches!(pointer.offset.view(), OffsetView::Constant(0)))
            .map(|(pointer, value)| (pointer.clone(), value.native().clone()))
            .chain(run_slots)
            .filter_map(|(pointer, value)| {
                self.locals
                    .name_for_slot(&pointer)
                    .map(|name| (pointer, name, value))
            })
            .collect::<Vec<_>>();
        values.sort_by(|left, right| left.0.cmp(&right.0));
        values.into_iter().map(|(_, name, value)| (name, value))
    }

    /// A speculative spelling lookup visits only declared local slots. It
    /// borrows each atom, never materializing all local values or array runs.
    /// Slot order retains the same deterministic first name as local_cell_values.
    pub(crate) fn local_name_holding_bitvector_variable(
        &self,
        variable: Variable,
    ) -> Option<&BindingName> {
        // The candidates are the scalar locals bound to the variable, found
        // through the held-term index; each must still hold it in current
        // memory at its slot's start. The first such slot answers.
        let term = OldMachineTerm::Variable(variable);
        let mut held = None;
        for name in self.locals.names_holding_integer(&term) {
            if crate::instrumentation::deadline_exceeded() {
                return None;
            }
            let Some(pointer) = self.locals.slot(name) else {
                continue;
            };
            if matches!(pointer.offset.view(), OffsetView::Constant(0))
                && self.memory.cells.bitvector_variable_at(pointer) == Some(variable)
                && held.is_none_or(|(first, _): (&Address, &BindingName)| pointer < first)
            {
                held = Some((pointer, name));
            }
        }
        held.map(|(_, name)| name)
    }

    /// An atom's recorded load address selects one local slot directly.
    pub(crate) fn local_name_holding_bitvector_variable_at(
        &self,
        variable: Variable,
        pointer: &Address,
    ) -> Option<&BindingName> {
        if crate::instrumentation::deadline_exceeded() {
            return None;
        }
        let name = self.locals.name_for_slot(pointer)?;
        // An array or aggregate's name denotes the object, not its first
        // element, though its slot is that element's address.
        if self.locals.is_array_object(name) || self.locals.is_aggregate_object(name) {
            return None;
        }
        (self.memory.cells.bitvector_variable_at(pointer) == Some(variable)).then_some(name)
    }

    /// Refresh caller scalar bindings after call-site code has modified their
    /// address-backed cells. Ordinary function frames keep their own local
    /// environment, but inline bodies execute with a separate parameter
    /// environment while retaining the caller's memory.
    /// The cell delta selects exact local slots. A changed run selects the
    /// slots indexed under its block without enumerating the run's elements.
    /// Certified stores also refresh a slot invalidated by a partial write.
    pub(in crate::kernel) fn sync_changed_scalar_locals(&mut self, before: &SymbolicMemory) {
        let cells = &self.memory.cells;
        let mut names = cells
            .concrete()
            .diff(before.cells.concrete())
            .filter_map(|change| self.locals.name_for_slot(change.key()))
            .collect::<std::collections::BTreeSet<_>>();
        for (old, new) in cells.run_diff(&before.cells) {
            let run = old.or(new).expect("changed run");
            names.extend(self.locals.names_with_slot_in(&run.base().base));
        }
        let updates = names
            .into_iter()
            .filter_map(|name| {
                let binding = self.locals.binding(name)?;
                let (program_type, slot, volatile, pointee_volatile, constant, pointee_constant) =
                    match binding {
                        LocalBinding::Object {
                            program_type,
                            slot,
                            volatile,
                            pointee_volatile,
                            constant,
                            pointee_constant,
                            ..
                        }
                        | LocalBinding::UninitializedObject {
                            program_type,
                            slot,
                            volatile,
                            pointee_volatile,
                            constant,
                            pointee_constant,
                            ..
                        } => (
                            *program_type,
                            slot.clone(),
                            *volatile,
                            *pointee_volatile,
                            *constant,
                            *pointee_constant,
                        ),
                        LocalBinding::GlobalObject { .. }
                        | LocalBinding::ArrayObject { .. }
                        | LocalBinding::AggregateObject { .. } => return None,
                    };
                // A store through a pointer to the other signedness of the
                // object's width wrote the same bits; the local reads them in
                // its own type (`ProgramType::read_cell`).
                let value = cells.get(&slot)?;
                program_type
                    .read_cell(&value)
                    .or_else(|| {
                        (!matches!(binding, LocalBinding::UninitializedObject { .. }))
                            .then_some(value)
                    })
                    .map(|value| {
                        (
                            name.clone(),
                            value,
                            program_type,
                            slot,
                            volatile,
                            pointee_volatile,
                            constant,
                            pointee_constant,
                        )
                    })
            })
            .collect::<Vec<_>>();
        for (
            name,
            value,
            program_type,
            slot,
            volatile,
            pointee_volatile,
            constant,
            pointee_constant,
        ) in updates
        {
            self.locals.set_typed_qualified_with_all_qualifiers(
                name,
                value,
                program_type,
                slot,
                volatile,
                pointee_volatile,
                constant,
                pointee_constant,
            );
        }
    }

    pub fn resources(&self) -> &ResourceContext {
        &self.resources
    }

    pub fn with_observed_population_family(mut self, name: impl Into<String>) -> Self {
        self.observed_population_families.insert(name.into());
        self
    }

    pub fn observes_population_family(&self, name: &str) -> bool {
        self.observed_population_families.contains(name)
    }

    /// The logical resource-state component used to index predicate facts.
    ///
    /// Predicate memory arguments retain their existing, explicit state
    /// representation. Keeping memory and locals out of this value prevents
    /// an unrelated C step from changing the identity of a predicate merely
    /// because the predicate language can also observe resource counts.
    pub fn resource_state_source(&self) -> Self {
        Self {
            population_effects: Arc::new(PopulationEffects {
                // Nested predicates recapture the same logical model.
                // Their execution resource context is intentionally empty;
                // keep the original count-only witness instead of using it.
                predicate_count_permissions: Some(
                    self.population_effects
                        .predicate_count_permissions
                        .clone()
                        .unwrap_or_else(|| {
                            PredicateCountPermissions(Arc::new(self.resources.clone()))
                        }),
                ),
                creation: self.population_effects.creation.clone(),
            }),
            ..Self::new()
        }
    }
}

thread_local! {
    /// The alignment the compiler gives each file-scope or static object's
    /// block, recorded once when the block is created. Alignment of such a
    /// block is intrinsic, like a heap block's, so the decision consults
    /// this instead of a path fact on every implicit address-of read.
    static BLOCK_ALIGNMENT_REGISTRY: std::cell::RefCell<BTreeMap<AddressBase, u64>> =
        const { std::cell::RefCell::new(BTreeMap::new()) };
}

thread_local! {
    /// Where the argument copied into each by-value aggregate parameter's
    /// frame block arrived. The callee's copy and the caller's argument are
    /// two objects; a diagnostic reads this to name the second. Nothing
    /// that decides a proof reads it.
    static AGGREGATE_ARGUMENT_SOURCES: std::cell::RefCell<BTreeMap<AddressBase, Address>> =
        const { std::cell::RefCell::new(BTreeMap::new()) };
}

/// Records that the aggregate parameter stored in `slot` was copied from
/// `source`. One entry per parameter bound; a later binding of the same
/// frame block replaces it.
pub(crate) fn register_aggregate_argument_source(slot: &AddressBase, source: &Address) {
    AGGREGATE_ARGUMENT_SOURCES.with(|sources| {
        sources.borrow_mut().insert(slot.clone(), source.clone());
    });
}

pub(crate) fn registered_aggregate_argument_source(slot: &AddressBase) -> Option<Address> {
    AGGREGATE_ARGUMENT_SOURCES.with(|sources| sources.borrow().get(slot).cloned())
}

pub(crate) fn register_block_alignment(block: &AddressBase, alignment: u32) {
    if alignment < 2 {
        return;
    }
    BLOCK_ALIGNMENT_REGISTRY.with(|registry| {
        registry
            .borrow_mut()
            .insert(block.clone(), u64::from(alignment));
    });
}

pub(crate) fn registered_block_alignment(block: &AddressBase) -> Option<u64> {
    BLOCK_ALIGNMENT_REGISTRY.with(|registry| registry.borrow().get(block).copied())
}

/// Look up an intrinsic block alignment after charging the bounded key
/// payload and logarithmic ordered-map search. Callers must validate the key
/// payload before invoking this helper; the charge here accounts for the
/// registry lookup itself and never scans unrelated entries.
pub(crate) fn registered_block_alignment_charged(
    block: &AddressBase,
    key_payload: usize,
) -> Option<u64> {
    BLOCK_ALIGNMENT_REGISTRY.with(|registry| {
        let registry = registry.borrow();
        let comparisons = (usize::BITS - registry.len().max(1).leading_zeros()) as usize;
        if crate::instrumentation::deadline_exceeded_with_work(
            key_payload.saturating_mul(comparisons).max(1),
        ) {
            return None;
        }
        registry.get(block).copied()
    })
}

/// The block-alignment registry and the never-address-taken locals, as one
/// value a reusable session captures and restores.
#[derive(Clone)]
pub(crate) struct BlockRegistriesState {
    alignment: BTreeMap<AddressBase, u64>,
    never_address_taken: BTreeSet<BindingName>,
    never_address_taken_key: std::sync::Arc<()>,
}

pub(crate) fn capture_block_registries() -> BlockRegistriesState {
    BlockRegistriesState {
        alignment: BLOCK_ALIGNMENT_REGISTRY.with(|registry| registry.borrow().clone()),
        never_address_taken: NEVER_ADDRESS_TAKEN_LOCALS.with(|registry| registry.borrow().clone()),
        never_address_taken_key: never_address_taken_locals_key(),
    }
}

pub(crate) fn restore_block_registries(state: &BlockRegistriesState) {
    NEVER_ADDRESS_TAKEN_LOCALS_KEY
        .with(|key| *key.borrow_mut() = state.never_address_taken_key.clone());
    BLOCK_ALIGNMENT_REGISTRY.with(|registry| *registry.borrow_mut() = state.alignment.clone());
    NEVER_ADDRESS_TAKEN_LOCALS
        .with(|registry| *registry.borrow_mut() = state.never_address_taken.clone());
    advance_never_address_taken_generation();
}

pub(crate) fn clear_block_alignment_registry() {
    BLOCK_ALIGNMENT_REGISTRY.with(|registry| registry.borrow_mut().clear());
}

thread_local! {
    static NEVER_ADDRESS_TAKEN_GENERATION: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// Automatic declarations whose address the selected source never takes.
    /// Typed C IDs distinguish functions and lexical scopes, independently of
    /// source spelling and storage-instance counters. Legacy Named bindings
    /// keep the conservative program-wide treatment of the other frontends.
    /// Populated by the source pre-pass before any query. Missing declarations
    /// are addressable by default; a session revision scopes resolution caches.
    static NEVER_ADDRESS_TAKEN_LOCALS_KEY: std::cell::RefCell<std::sync::Arc<()>> = std::cell::RefCell::new(std::sync::Arc::new(()));
    static NEVER_ADDRESS_TAKEN_LOCALS: std::cell::RefCell<BTreeSet<BindingName>> =
        const { std::cell::RefCell::new(BTreeSet::new()) };
}

/// Globally unique revisions also distinguish registries on different threads.
fn advance_never_address_taken_generation() {
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
    let revision = NEXT
        .fetch_update(
            std::sync::atomic::Ordering::Relaxed,
            std::sync::atomic::Ordering::Relaxed,
            |value| value.checked_add(1),
        )
        .expect("addressability revision space exhausted");
    NEVER_ADDRESS_TAKEN_GENERATION.with(|generation| generation.set(revision));
}

pub(super) fn never_address_taken_generation() -> u64 {
    NEVER_ADDRESS_TAKEN_GENERATION.with(std::cell::Cell::get)
}

/// Records the program-wide never-address-taken names for this session. The
/// surface computes them from every function body it parsed; see
/// `crate::languages::c::address_taken::summarize_address_taken`.
pub(crate) fn never_address_taken_locals_key() -> std::sync::Arc<()> {
    NEVER_ADDRESS_TAKEN_LOCALS_KEY.with(|key| key.borrow().clone())
}

pub(crate) fn set_never_address_taken_locals(names: BTreeSet<BindingName>) {
    NEVER_ADDRESS_TAKEN_LOCALS_KEY.with(|key| *key.borrow_mut() = std::sync::Arc::new(()));
    NEVER_ADDRESS_TAKEN_LOCALS.with(|registry| *registry.borrow_mut() = names);
    advance_never_address_taken_generation();
}

/// Withdraws names a later source bundle shows to be address-taken, for a
/// verification that joins an enclosing session instead of starting one.
///
/// Returns whether anything was withdrawn, so the caller can drop the memo
/// tables that may already hold an answer computed while the name was still
/// in the registry. Today no caller joins a session with different sources,
/// and this keeps that from becoming a silent staleness bug if one appears.
pub(crate) fn withdraw_never_address_taken_locals(taken: &BTreeSet<BindingName>) -> bool {
    let changed = NEVER_ADDRESS_TAKEN_LOCALS.with(|registry| {
        let mut registry = registry.borrow_mut();
        let before = registry.len();
        registry.retain(|name| !taken.contains(name));
        registry.len() != before
    });
    if changed {
        NEVER_ADDRESS_TAKEN_LOCALS_KEY.with(|key| *key.borrow_mut() = std::sync::Arc::new(()));
        advance_never_address_taken_generation();
    }
    changed
}

/// The declaration a storage block belongs to. Typed blocks carry this
/// directly; legacy blocks retain their original prefix grammar.
fn local_block_object_name(block: &AddressBase) -> Option<BindingName> {
    match block {
        AddressBase::AutomaticLocal { binding, .. } => return Some(binding.clone().into()),
        AddressBase::SliceLength { slice, .. } => {
            return Some(BindingName::SliceLength(slice.clone()));
        }
        _ => {}
    }
    let rest = block.strip_prefix("local:")?;
    match rest.split_once(':') {
        None => Some(rest.into()),
        Some(("lifetime" | "frame", tail)) => {
            let (_, name) = tail.split_once(':')?;
            (!name.contains(':')).then(|| name.into())
        }
        Some(_) => None,
    }
}

/// Whether this block holds an automatic object whose address no function in
/// this session's C sources takes.
///
/// Soundness. C gives a program exactly two ways to obtain the address of an
/// automatic object: the `&` operator, and the array-to-pointer conversion of
/// an array or aggregate object's name. The pre-pass behind this registry
/// refuses a name that is ever declared with an array, struct or union type,
/// and refuses a name that occurs anywhere under an address-of node in any
/// function body, so neither way is available for a name that survives into
/// it. No other pointer can reach the object either: arithmetic that leaves
/// the object it was derived from is undefined behaviour, which Click enforces
/// with the bounds obligation on every displaced access
/// (`MemoryCanStore` / `access_in_bounds`), and an integer cast to a pointer
/// is outside the supported C subset. A `&x` written in a *proof* creates no
/// runtime pointer, so an annotation cannot make an object addressable that
/// the program never addresses.
///
/// This is therefore a claim about addressability, not about one pair of
/// pointers: a never-address-taken object is not memory any pointer value can
/// designate. The caller must still defer to an equality the context *states*
/// about the pointer, because an assumed `p == &x` would otherwise be refuted
/// and the context silently made inconsistent.
pub(crate) fn block_is_never_address_taken_local(block: &AddressBase) -> bool {
    let Some(name) = local_block_object_name(block) else {
        return false;
    };
    NEVER_ADDRESS_TAKEN_LOCALS.with(|registry| registry.borrow().contains(&name))
}

pub(crate) fn clear_never_address_taken_locals() {
    NEVER_ADDRESS_TAKEN_LOCALS_KEY.with(|key| *key.borrow_mut() = std::sync::Arc::new(()));
    NEVER_ADDRESS_TAKEN_LOCALS.with(|registry| registry.borrow_mut().clear());
    advance_never_address_taken_generation();
}

#[cfg(test)]
mod hidden_local_distinctness_tests {
    use super::*;

    /// A pointer value of any provenance is distinct from a local whose
    /// address is never taken, and still not from one whose address is.
    #[test]
    fn a_pointer_value_never_reaches_a_local_whose_address_is_never_taken() {
        set_never_address_taken_locals(BTreeSet::from(["hidden".into()]));
        let hidden: AddressBase = "local:hidden".into();
        let taken: AddressBase = "local:taken".into();
        for value in [
            AddressBase::Symbolic(Variable(7)),
            AddressBase::FunctionSymbolic(Variable(8)),
            AddressBase::ExternalObject(Variable(9)),
            AddressBase::ExternalArgument,
        ] {
            assert!(value.proven_distinct(&hidden), "{value:?}");
            assert!(hidden.proven_distinct(&value), "{value:?}");
        }
        assert!(!AddressBase::Symbolic(Variable(7)).proven_distinct(&taken));
        clear_never_address_taken_locals();
        assert!(!AddressBase::Symbolic(Variable(7)).proven_distinct(&hidden));
    }
}

#[cfg(test)]
mod contract_retirement_tests {
    use super::*;

    #[test]
    fn retirement_drops_zeroed_status_under_each_equal_base_spelling() {
        let base = Address::new(AddressBase::Heap(922_200), AddressOffset::constant(0));
        let aliases = [
            Address::new(
                AddressBase::Symbolic(Variable(922_201)),
                AddressOffset::constant(0),
            ),
            Address::new(
                AddressBase::Symbolic(Variable(922_202)),
                AddressOffset::constant(4),
            ),
        ];
        let unrelated = Address::new(AddressBase::Heap(922_203), AddressOffset::constant(0));
        let assumptions = aliases.iter().fold(PureFactContext::new(), |facts, alias| {
            facts.assume_proposition(Proposition::condition_is(
                OldConditionTerm::address_equal(alias.clone(), base.clone()),
                true,
            ))
        });
        let mut memory = SymbolicMemory::new()
            .with_heap_allocation_claim(base.clone(), AllocationSize::int32(4))
            .expect("fresh input allocation");
        let heap = std::sync::Arc::make_mut(&mut memory.heap);
        heap.zeroed_allocations.extend(aliases.iter().cloned());
        heap.zeroed_allocations.insert(unrelated.clone());
        memory = memory.store_with_context(aliases[0].clone(), int32(9), &assumptions);
        memory = memory.store(unrelated.clone(), int32(11));
        assert!(memory.has_initialized_bytes_at(&aliases[0], 4));
        let retired = memory.retire_contract_heap_allocation_claim(
            &base,
            &OldMachineTerm::constant(4),
            &assumptions,
        );
        for alias in &aliases {
            assert!(
                !retired.heap.zeroed_allocations.contains(alias),
                "no equal spelling may retain a blanket zeroed reading"
            );
        }
        assert!(retired.heap.zeroed_allocations.contains(&unrelated));
        assert_eq!(retired.known_value(&aliases[0]), None);
        assert!(!retired.has_initialized_bytes_at(&aliases[0], 4));
        assert_eq!(retired.known_value(&unrelated), Some(int32(11)));
    }
}

#[cfg(test)]
mod union_store_tests {
    use super::*;

    /// A direct member store invalidates every overlapping old member view.
    #[test]
    fn union_store_invalidates_the_other_members_stale_overlay() {
        let base = Address::new(
            AddressBase::Concrete("local:u".to_string()),
            AddressOffset::constant(0),
        );
        let memory = SymbolicMemory::new()
            .store_union(base.clone(), ProgramType::UInt8, crate::kernel::uint8(0xAA))
            .store_union(
                base.clone(),
                ProgramType::Int32,
                ProgramValue::Int32(OldMachineTerm::constant(0x51)),
            );
        assert_eq!(
            memory.known_union_value(&base, ProgramType::UInt8),
            None,
            "the old byte view must not survive the wider member write"
        );
        assert_eq!(
            memory.known_union_value(&base, ProgramType::Int32),
            Some(ProgramValue::Int32(OldMachineTerm::constant(0x51))),
        );
    }
}

#[cfg(test)]
mod interface_join_tombstone_tests {
    use super::*;

    /// A join retains a tombstone if any incoming arm freed the allocation,
    /// even when another arm still lists it as potentially live. A later
    /// dereference through the alias must be rejected until the paths are
    /// distinguished.
    #[test]
    fn interface_join_keeps_one_arm_deallocation() {
        let base = Address::new(AddressBase::Heap(923_001), AddressOffset::constant(0));
        // Arm B kept it live.
        let alive = SymbolicMemory::new()
            .with_block(base.base.clone(), 8)
            .with_heap_allocation_claim(base.clone(), AllocationSize::int32(8))
            .expect("fresh allocation on arm B");
        // Arm A freed it.
        let freed = alive
            .clone()
            .free_heap_block(&base, &PureFactContext::new())
            .expect("the allocation frees on arm A");
        let arms = [&alive, &freed];
        let joined = alive
            .clone()
            .with_interface_memory_havoc_preserving_borrows(
                Variable(923_100),
                &BTreeSet::new(),
                &arms,
                None,
            )
            .expect("the interface join should run");
        assert!(
            joined.heap.live_allocations.contains_key(&base),
            "the join unions the live arm's record"
        );
        assert!(
            joined.heap.deallocated_allocations.contains_key(&base),
            "the deallocating arm's tombstone must survive the join"
        );
        assert!(
            joined.is_deallocated_heap_address(&base, &PureFactContext::new()),
            "an alias of the possibly-freed allocation must be rejected at the join"
        );
    }
}

#[cfg(test)]
mod join_allocation_spelling_tests {
    use super::*;

    fn heap_base(identity: u64) -> Address {
        Address::new(AddressBase::Heap(identity), AddressOffset::constant(0))
    }

    /// Each arm holds its allocation live under its own spelling, so the
    /// join unions two live entries.
    fn joined(p: &Address, q: &Address) -> SymbolicMemory {
        let arm_a = SymbolicMemory::new()
            .with_block(p.base.clone(), 8)
            .with_heap_allocation_claim(p.clone(), AllocationSize::int32(8))
            .expect("arm A claim");
        let arm_b = SymbolicMemory::new()
            .with_block(q.base.clone(), 8)
            .with_heap_allocation_claim(q.clone(), AllocationSize::int32(8))
            .expect("arm B claim");
        let arms = [&arm_a, &arm_b];
        let joined = arm_a
            .clone()
            .with_interface_memory_havoc_preserving_borrows(
                Variable(924_100),
                &BTreeSet::new(),
                &arms,
                None,
            )
            .expect("the join runs");
        assert!(joined.heap.live_allocations.contains_key(p));
        assert!(joined.heap.live_allocations.contains_key(q));
        joined
    }

    /// `with_interface_memory_havoc_preserving_borrows` keys `live_allocations`
    /// by pointer spelling, so one allocation the arms spell `p` and `q`
    /// joins as two live entries. Where `p == q` is known, a free through
    /// either spelling retires both, and the other spelling cannot be freed
    /// or reported live afterwards.
    #[test]
    fn join_of_two_spellings_of_one_allocation_frees_once() {
        let p = heap_base(924_001);
        let q = Address::new(
            AddressBase::Symbolic(Variable(924_005)),
            AddressOffset::constant(0),
        );
        let assumptions = PureFactContext::new().assume_proposition(Proposition::condition_is(
            OldConditionTerm::address_equal(p.clone(), q.clone()),
            true,
        ));
        assert!(!assumptions.is_inconsistent());
        for (first, second) in [(&p, &q), (&q, &p)] {
            let once = joined(&p, &q)
                .free_heap_block(first, &assumptions)
                .expect("the first free is a real free");
            assert!(!once.heap.live_allocations.contains_key(second));
            assert!(!once.is_live_heap_address(second, &assumptions));
            assert!(once.is_deallocated_heap_address(second, &assumptions));
            assert!(once.free_heap_block(second, &assumptions).is_err());
        }
    }

    /// Two fresh heap identities are never one allocation: their equality
    /// is not an alias fact but a contradiction, under which the path the
    /// frees are on does not exist.
    #[test]
    fn equal_fresh_heap_identities_are_a_contradiction() {
        let p = heap_base(924_021);
        let q = heap_base(924_025);
        assert_eq!(
            OldConditionTerm::address_equal(p.clone(), q.clone()),
            OldConditionTerm::Constant(false)
        );
        let assumptions = PureFactContext::new().assume_proposition(Proposition::condition_is(
            OldConditionTerm::address_equal(p, q),
            true,
        ));
        assert!(assumptions.is_inconsistent());
    }

    #[test]
    fn join_of_two_different_allocations_frees_each_once() {
        let p = heap_base(924_011);
        let q = heap_base(924_015);
        let assumptions = PureFactContext::new();
        let once = joined(&p, &q)
            .free_heap_block(&p, &assumptions)
            .expect("the first allocation frees");
        assert!(once.heap.live_allocations.contains_key(&q));
        let twice = once
            .free_heap_block(&q, &assumptions)
            .expect("the second allocation frees");
        assert!(matches!(
            twice.free_heap_block(&q, &assumptions),
            Err(InvalidFree::DoubleFree)
        ));
    }
}

/// One cached value a forgetting transition is asked about
/// ([`SymbolicMemory::forget_cached_values`]).
#[derive(Clone, Copy, Debug)]
pub(super) enum CachedValue<'a> {
    /// A cell, or one slot of a run.
    Cell(&'a ProgramValue),
    /// A typed view of union storage, keyed by the member type it records.
    UnionView(ProgramType, &'a ProgramValue),
}

impl<'a> CachedValue<'a> {
    pub(super) fn value(self) -> &'a ProgramValue {
        match self {
            Self::Cell(value) | Self::UnionView(_, value) => value,
        }
    }

    /// The width of the access this value answers. A union view has no
    /// value width of its own to trust, so it stands in its key type's.
    pub(super) fn byte_width(self) -> u32 {
        match self {
            Self::Cell(value) => value.byte_width(),
            Self::UnionView(program_type, _) => program_type.byte_width(),
        }
    }
}

/// What a forgetting transition does with one cached value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum CachedValueFate {
    /// The value is still what the memory holds there.
    Kept,
    /// The value goes because the write about to run replaces every one of
    /// its bytes: it is stale, and nothing about the memory is lost.
    Overwritten,
    /// The value goes with its storage, whose retirement the caller records.
    Retired,
    /// The value goes and its bytes are no longer known.
    Forgotten,
}

/// Which cached values a forgetting transition asks about; every other one
/// is kept unasked.
#[derive(Clone, Copy)]
pub(super) enum ForgetScope<'a> {
    Ordered {
        candidates: &'a AliasCandidates,
        selected: &'a [Address],
        cells_kept: &'a [(Address, Address)],
        runs: Option<&'a [cell_store::RunKey]>,
    },
    /// Every cached value, for a transition that may have written anywhere.
    Everywhere,
    /// The values in `candidates`' blocks, except the cells inside the key
    /// ranges `cells_kept`, which the caller has shown its rule keeps
    /// ([`CellStore::retain_candidates_outside_by`]).
    Candidates {
        candidates: &'a AliasCandidates,
        cells_kept: &'a [(Address, Address)],
    },
}

impl<'a> ForgetScope<'a> {
    fn candidates(candidates: &'a AliasCandidates) -> Self {
        Self::Candidates {
            candidates,
            cells_kept: &[],
        }
    }
}

/// The whole-run answer of a rule that has no cheaper one: ask every slot.
fn ask_every_slot(_: &CellRun) -> (SlotSet, crate::kernel::primitives::RuleAnswer) {
    (
        SlotSet::PerSlot,
        crate::kernel::primitives::RuleAnswer::Exact,
    )
}

/// Collects one dropped cell for [`SymbolicMemory::record_dropped_initialized_cells`],
/// except from inside a debug self-check that re-asks a retain predicate:
/// that would record, in a debug build only, cells a release build keeps
/// by a whole-run answer.
fn push_dropped_initialized(dropped: &mut Vec<(Address, u32)>, cell: (Address, u32)) {
    if !crate::instrumentation::in_uncharged_debug_check() {
        dropped.push(cell);
    }
}

/// The entries of automatic (`local:`) blocks in a pointer-keyed map, which
/// are one contiguous key range: `local:` blocks are `Concrete` names sharing
/// that prefix.
fn local_block_entries<'a, K: BlockKeyed, V>(
    map: &'a HashedOrdMap<K, V>,
) -> impl Iterator<Item = (&'a K, &'a V)> + 'a {
    map.range(K::first_key_of(&AddressBase::from("local:"))..)
        .take_while(|(key, _)| key.key_block().is_local_block())
}

#[cfg(test)]
mod initialization_record_tests {
    use super::*;

    #[test]
    fn unwritten_output_keeps_forgotten_external_input_fields_initialized() {
        let _session = crate::kernel::VerificationSession::enter();
        let output = Address::symbolic(Variable(924_040));
        for field in [
            Address::symbolic(Variable(924_041)),
            Address::new(
                AddressBase::ExternalArgument,
                AddressOffset::scale_int32(OldMachineTerm::Variable(Variable(924_042)), 4),
            ),
        ] {
            for seeded in [false, true] {
                let input = if seeded {
                    SymbolicMemory::new().with_seeded_cells(
                        field.clone(),
                        8,
                        ProgramType::UInt8Pointer,
                        0,
                        1,
                        intern_memory(SymbolicMemory::new()),
                    )
                } else {
                    SymbolicMemory::new()
                        .store(field.clone(), ProgramValue::pointer(Address::null()))
                };
                assert!(!input.has_initialized_bytes_at(&field, 8));
                let before = input.with_uninitialized_object(output.clone(), 4);
                let after =
                    before.without_possible_aliasing_cells(&output, 1, &PureFactContext::new());
                assert!(after.known_value(&field).is_none());
                assert!(
                    after.has_initialized_bytes_at(&field, 8),
                    "seeded={seeded}: {field:?}"
                );
                assert!(!after.has_initialized_bytes_at(&field, 9));
                assert!(!after.has_initialized_bytes_at(&output.offset_by_bytes(1), 1));
            }
        }
    }

    #[test]
    fn forgotten_external_observations_preserve_only_the_bytes_observed() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Address::symbolic(Variable(924_043));
        let output = Address::symbolic(Variable(924_044));
        for count in [0, 1, 2] {
            let before = SymbolicMemory::new()
                .with_seeded_cells(
                    field.clone(),
                    4,
                    ProgramType::Int32,
                    0,
                    count,
                    intern_memory(SymbolicMemory::new()),
                )
                .with_uninitialized_object(output.clone(), 4);
            let after = before.without_possible_aliasing_cells(&output, 1, &PureFactContext::new());
            assert_eq!(after.has_initialized_bytes_at(&field, 8), count == 2);
            assert_eq!(after.has_initialized_bytes_at(&field, 4), count != 0);
            assert!(!after.has_initialized_bytes_at(&field, 9));
        }
    }

    fn element(block: &str, index: i64) -> Address {
        Address::new(AddressBase::from(block), AddressOffset::constant(4 * index))
    }

    fn unplaced(block: &str) -> Address {
        Address::new(
            AddressBase::from(block),
            AddressOffset::scale_int32(OldMachineTerm::Variable(Variable(924_001)), 4),
        )
    }

    fn written_pair(block: &str) -> SymbolicMemory {
        SymbolicMemory::new()
            .with_block(block, 8)
            .store(
                element(block, 0),
                ProgramValue::Int32(OldMachineTerm::constant(5)),
            )
            .store(
                element(block, 1),
                ProgramValue::Int32(OldMachineTerm::constant(5)),
            )
    }

    fn forgotten_pair(block: &str) -> SymbolicMemory {
        written_pair(block).without_possible_aliasing_cells(
            &unplaced(block),
            4,
            &PureFactContext::new(),
        )
    }

    #[test]
    fn an_unplaced_store_keeps_the_bytes_it_forgets_initialized() {
        let block = "local:record-pair";
        assert!(!written_pair(block).has_initialized_bytes_at(&element(block, 0), 4));
        let forgotten = forgotten_pair(block);
        assert!(!forgotten.has_known_cell_at(&element(block, 0)));
        assert!(forgotten.has_initialized_bytes_at(&element(block, 0), 8));
        assert!(!forgotten.has_initialized_bytes_at(&element(block, 1), 8));
        // The store the forgetting precedes only initializes more.
        let stored = forgotten.store(
            unplaced(block),
            ProgramValue::Int32(OldMachineTerm::constant(7)),
        );
        assert!(stored.has_initialized_bytes_at(&element(block, 0), 8));
    }

    #[test]
    fn loop_havoc_keeps_forgotten_automatic_bytes_initialized() {
        let block = "local:record-loop";
        let havoc = written_pair(block).with_loop_memory_havoc_preserving_borrows(
            Variable(924_002),
            &BTreeSet::new(),
            None,
            None,
        );
        assert!(!havoc.has_known_cell_at(&element(block, 1)));
        assert!(havoc.has_initialized_bytes_at(&element(block, 0), 8));
    }

    #[test]
    fn a_join_keeps_only_bytes_every_arm_initialized() {
        let block = "local:record-join";
        // One arm forgot both values but keeps their initialization; the
        // other still caches only the first element.
        let forgotten = forgotten_pair(block);
        let first_only = SymbolicMemory::new().with_block(block, 8).store(
            element(block, 0),
            ProgramValue::Int32(OldMachineTerm::constant(5)),
        );
        let arms = [&forgotten, &first_only];
        let joined = forgotten
            .clone()
            .with_interface_memory_havoc_preserving_borrows(
                Variable(924_003),
                &BTreeSet::new(),
                &arms,
                None,
            )
            .expect("the interface join should run");
        assert!(joined.has_initialized_bytes_at(&element(block, 0), 4));
        assert!(!joined.has_initialized_bytes_at(&element(block, 1), 4));
    }

    /// A fresh local block of `count` two-field structs (`stride` 8) or
    /// `count` int32s (`stride` 4), its zero contents seeded as constant runs
    /// with no initialization recorded, so only the runs say it was written.
    fn zero_runs(block: &str, count: u32, stride: u32) -> SymbolicMemory {
        let zero = ProgramValue::Int32(OldMachineTerm::constant(0));
        let runs = (0..stride / 4)
            .map(|field| ConstantRun {
                offset: 4 * field,
                stride,
                count,
                value: zero.clone(),
            })
            .collect::<Vec<_>>();
        SymbolicMemory::new()
            .with_block(block, count * stride)
            .with_constant_runs(&element(block, 0), &runs)
            .expect("a fresh local block takes constant runs")
    }

    fn loop_havoc(memory: SymbolicMemory, variable: u64) -> SymbolicMemory {
        memory.with_loop_memory_havoc_preserving_borrows(
            Variable(variable),
            &BTreeSet::new(),
            None,
            None,
        )
    }

    #[test]
    fn loop_havoc_keeps_a_dropped_run_initialized() {
        for (block, stride) in [("local:record-run", 4), ("local:record-strided-run", 8)] {
            let memory = zero_runs(block, 4, stride);
            assert!(!memory.has_initialized_bytes_at(&element(block, 0), 4));
            let havoc = loop_havoc(memory, 924_005);
            assert!(!havoc.has_known_cell_at(&element(block, 3)));
            assert!(havoc.has_initialized_bytes_at(&element(block, 0), 4 * stride));
            assert!(!havoc.has_initialized_bytes_at(&element(block, 0), 4 * stride + 1));
        }
    }

    #[test]
    fn an_ended_lifetime_forgets_its_initialization() {
        let block = "local:record-lifetime";
        let forgotten = forgotten_pair(block);
        assert!(forgotten.has_initialized_bytes_at(&element(block, 0), 4));
        let ended = forgotten.without_local_block(&AddressBase::from(block));
        assert!(!ended.has_initialized_bytes_at(&element(block, 0), 4));
    }

    #[test]
    fn an_element_index_the_facts_bound_reads_a_covering_run() {
        let block = "local:record-index";
        let forgotten = forgotten_pair(block);
        let index = OldMachineTerm::Variable(Variable(924_004));
        let read = Address::new(
            AddressBase::from(block),
            AddressOffset::scale_int32(index.clone(), 4),
        );
        let bounded = |high: u32| {
            PureFactContext::new()
                .assume_condition(
                    OldConditionTerm::signed_less_equal(OldMachineTerm::constant(0), index.clone()),
                    true,
                )
                .assume_condition(
                    OldConditionTerm::signed_less_equal(
                        index.clone(),
                        OldMachineTerm::constant(high),
                    ),
                    true,
                )
        };
        assert!(forgotten.has_initialized_bytes_under(&read, 4, &bounded(1)));
        assert!(!forgotten.has_initialized_bytes_under(&read, 4, &bounded(2)));
        assert!(!forgotten.has_initialized_bytes_under(&read, 4, &PureFactContext::new()));
    }

    fn index_between(index: &OldMachineTerm, low: u32, high: u32) -> PureFactContext {
        PureFactContext::new()
            .assume_condition(
                OldConditionTerm::signed_less_equal(OldMachineTerm::constant(low), index.clone()),
                true,
            )
            .assume_condition(
                OldConditionTerm::signed_less_equal(index.clone(), OldMachineTerm::constant(high)),
                true,
            )
    }

    #[test]
    fn cached_cells_cover_an_element_index_the_facts_bound() {
        // Stores that still hold their values wrote their bytes: with no
        // initialization record at all, cells covering every element the
        // index may name cover the read, and a gap does not.
        let block = "local:record-cells";
        let written = written_pair(block);
        assert!(!written.has_initialized_bytes_at(&element(block, 0), 8));
        let index = OldMachineTerm::Variable(Variable(924_007));
        let read = Address::new(
            AddressBase::from(block),
            AddressOffset::scale_int32(index.clone(), 4),
        );
        assert!(written.has_initialized_bytes_under(&read, 4, &index_between(&index, 0, 1)));
        assert!(!written.has_initialized_bytes_under(&read, 4, &index_between(&index, 0, 2)));
        let gap = SymbolicMemory::new()
            .with_block(block, 12)
            .store(
                element(block, 0),
                ProgramValue::Int32(OldMachineTerm::constant(5)),
            )
            .store(
                element(block, 2),
                ProgramValue::Int32(OldMachineTerm::constant(5)),
            );
        assert!(!gap.has_initialized_bytes_under(&read, 4, &index_between(&index, 0, 2)));
        assert!(gap.has_initialized_bytes_under(&read, 4, &index_between(&index, 2, 2)));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/primitives/memory_state/initialization_record_tests.rs"
        );
    }
}

#[cfg(test)]
mod local_variable_spelling_tests {
    use super::*;

    fn scalar(state: ExecutionState, name: &str, value: ProgramValue) -> ExecutionState {
        let memory = state
            .memory()
            .clone()
            .store(SymbolicMemory::local_pointer(name), value.clone());
        state.with_local(name, value).with_memory(memory)
    }

    #[test]
    fn pointer_object_index_tracks_rebindings_and_scope_changes() {
        let blocks = [
            AddressBase::Symbolic(Variable(971_030)),
            AddressBase::Symbolic(Variable(971_031)),
        ];
        let mut locals = LocalEnvironment::new();
        for step in 0..60usize {
            let name = format!("p{}", step % 7);
            if step % 5 == 0 {
                locals.remove(&name);
            } else if step % 5 == 1 {
                locals.set(&name, int32(7));
            } else {
                locals.set(
                    &name,
                    ProgramValue::pointer(Address::new(
                        blocks[step % 2].clone(),
                        AddressOffset::constant(step as i64),
                    )),
                );
            }
            if step % 11 == 0 {
                locals.forget_initialization(&name);
            }
            let saved = locals.clone();
            if let Some(binding) = locals.binding(&name).cloned() {
                locals.remove(&name);
                locals.restore_binding(&name, binding);
            }
            let rebuilt =
                LocalEnvironment::from_parts(locals.bindings.clone(), locals.slots.clone());
            for block in &blocks {
                let scanned = locals
                    .object_values()
                    .filter_map(|(name, value)| {
                        let pointer = value.pointer()?.address();
                        (&pointer.base == block).then(|| (name, pointer.clone()))
                    })
                    .collect::<Vec<_>>();
                for indexed in [&locals, &saved, &rebuilt] {
                    assert_eq!(
                        indexed
                            .pointer_objects_in_block(block)
                            .map(|(name, pointer)| (name, pointer.address().clone()))
                            .collect::<Vec<_>>(),
                        scanned
                    );
                }
            }
        }
    }

    #[test]
    fn held_term_index_agrees_with_a_scan_of_the_bindings() {
        let x = OldMachineTerm::Variable(Variable(971_020));
        let y = OldMachineTerm::Variable(Variable(971_021));
        // Terms that share a fingerprint (same root and operand roots) but
        // differ deeper, beside equal terms held by several locals.
        let deep = |term: OldMachineTerm| {
            binary_node!(
                Int32,
                Add,
                Box::new(binary_node!(
                    Int32,
                    Add,
                    Box::new(term),
                    Box::new(x.clone())
                )),
                Box::new(OldMachineTerm::constant(1)),
            )
        };
        let terms = [
            x.clone(),
            y.clone(),
            deep(x.clone()),
            deep(y.clone()),
            OldMachineTerm::constant(7),
        ];
        let mut state = ExecutionState::new();
        for step in 0..60usize {
            let name = format!("v{}", step % 13);
            if step % 7 == 6 {
                state.locals.remove(&name);
            } else {
                let term = terms[step % terms.len()].clone();
                state = state.with_local(name, ProgramValue::Int32(term));
            }
        }
        state = state.with_local(
            "pointer",
            ProgramValue::pointer(SymbolicMemory::local_pointer("v0")),
        );
        for term in &terms {
            let scanned = state
                .locals()
                .object_values()
                .filter(|(_, value)| held_integer_term_of(value) == Some(term))
                .map(|(name, _)| name)
                .collect::<Vec<_>>();
            let indexed = state
                .locals()
                .names_holding_integer(term)
                .collect::<Vec<_>>();
            assert_eq!(indexed, scanned, "{term:?}");
        }
    }

    fn held_integer_term_of(value: &StoredExecutionValue) -> Option<&OldMachineTerm> {
        match value.native_payload()?.numeric_value() {
            crate::kernel::integer_c_value!(term) | ProgramValue::Bool(term) => Some(term),
            _ => None,
        }
    }

    #[test]
    fn local_variable_spelling_uses_current_memory_and_stable_slot_order() {
        let variable = Variable(971_010);
        let value = ProgramValue::UInt64(OldMachineTerm::Variable(variable));
        let state = scalar(
            scalar(ExecutionState::new(), "z", value.clone()),
            "a",
            value,
        );
        assert_eq!(
            state
                .local_name_holding_bitvector_variable(variable)
                .and_then(BindingName::named),
            Some("a")
        );
        let pointer = SymbolicMemory::local_pointer("a");
        assert_eq!(
            state
                .local_name_holding_bitvector_variable_at(variable, &pointer)
                .and_then(BindingName::named),
            Some("a")
        );
        let state = state.clone().with_memory(state.memory().clone().store(
            SymbolicMemory::local_pointer("a"),
            ProgramValue::UInt64(OldMachineTerm::uint64_constant(0)),
        ));
        assert_eq!(
            state
                .local_name_holding_bitvector_variable(variable)
                .and_then(BindingName::named),
            Some("z")
        );
        assert_eq!(
            state
                .local_name_holding_bitvector_variable_at(variable, &pointer)
                .and_then(BindingName::named),
            None,
            "a recorded address must still hold the atom in current memory"
        );
        let state = state.clone().with_memory(state.memory().clone().store(
            SymbolicMemory::local_pointer("z"),
            ProgramValue::UInt64(OldMachineTerm::uint64_constant(0)),
        ));
        assert_eq!(
            state
                .local_name_holding_bitvector_variable(variable)
                .and_then(BindingName::named),
            None
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/primitives/memory_state/local_variable_spelling_tests.rs"
        );
    }
}

#[cfg(test)]
mod kept_range_identity_tests {
    use super::*;

    fn ranges(id: u64) -> HashedOrdMap<MemoryRange, ()> {
        ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                Address::symbolic(Variable(id)),
                0.into(),
                4.into(),
            )))
            .flat_owned_memory_ranges()
            .clone()
    }

    #[test]
    fn kept_range_hash_collisions_use_exact_sets_across_threads() {
        let first = intern_kept_range_set_with_hash(ranges(7), HashedOrdMap::new(), 0);
        let same = intern_kept_range_set_with_hash(ranges(7), HashedOrdMap::new(), 0);
        let different = intern_kept_range_set_with_hash(ranges(8), HashedOrdMap::new(), 0);
        assert_eq!(first.id, same.id);
        assert_ne!(first.id, different.id);
        let across = std::thread::spawn(|| {
            intern_kept_range_set_with_hash(ranges(7), HashedOrdMap::new(), 0)
        })
        .join()
        .unwrap();
        assert_eq!(first.id, across.id);
    }

    #[test]
    fn kept_range_hash_collisions_distinguish_composite_exclusions() {
        let composite = ResourceContext::new().unchecked_with_fact(ResourceFact::own_composite(
            "boxed".into(),
            vec![ProgramValue::pointer(Address::symbolic(Variable(9)))],
        ));
        let intern = |original, introduced| {
            intern_kept_range_set_with_exclusions_and_hash(
                ranges(7),
                HashedOrdMap::new(),
                original,
                introduced,
                HashedOrdMap::new(),
                0,
            )
        };
        let original = ResourceContext::new()
            .unchecked_with_facts(ranges(8).keys().cloned().map(ResourceFact::own_memory));
        let original = original.memory_input_facts();
        let plain = intern(HashedOrdMap::new(), HashedOrdMap::new());
        let excluded = intern(original.clone(), HashedOrdMap::new());
        let introduced = intern(original.clone(), composite.owned_composite_facts().clone());
        assert_ne!(plain.id, excluded.id);
        assert_ne!(excluded.id, introduced.id);
        assert_eq!(
            introduced.id,
            intern(original.clone(), composite.owned_composite_facts().clone()).id
        );
    }

    #[test]
    fn kept_range_hash_collisions_distinguish_surviving_views() {
        let range = ranges(7).keys().next().unwrap().clone();
        let viewed = ResourceContext::new().unchecked_with_fact(ResourceFact::view_memory(range));
        let intern = |inputs| {
            intern_kept_range_set_with_exclusions_and_hash(
                HashedOrdMap::new(),
                HashedOrdMap::new(),
                HashedOrdMap::new(),
                HashedOrdMap::new(),
                inputs,
                0,
            )
        };
        let empty = intern(HashedOrdMap::new());
        let kept = intern(viewed.memory_input_facts().clone());
        assert_ne!(empty.id, kept.id);
        assert_eq!(kept.id, intern(viewed.memory_input_facts().clone()).id);
    }

    #[test]
    fn owned_range_index_keeps_duplicates_until_the_last_withdrawal() {
        let fact = ResourceFact::own_memory(MemoryRange::new(
            Address::symbolic(Variable(7)),
            0.into(),
            4.into(),
        ));
        let resources = ResourceContext::new().unchecked_with_facts([fact.clone(), fact.clone()]);
        let once = resources
            .without_fact(&fact, &PureFactContext::new())
            .unwrap();
        assert_eq!(once.flat_owned_memory_ranges().len(), 1);
        assert_eq!(once.memory_input_facts().len(), 1);
        let empty = once.without_fact(&fact, &PureFactContext::new()).unwrap();
        assert!(empty.flat_owned_memory_ranges().is_empty());
        assert!(empty.memory_input_facts().is_empty());
    }
}
