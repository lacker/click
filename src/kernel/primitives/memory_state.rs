use super::*;
use crate::kernel::CheckedPopulationAuthorityExchange;
use crate::kernel::CheckedPopulationMemberExchange;
use crate::kernel::ResourceDescription;
use std::fmt::Write;

fn memory_havoc_write_set_identity(mutable_ranges: &[CMemoryRange]) -> String {
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
    Pointer(Pointer),
    PointerOffset(PointerOffsetTerm),
    Bitvector(Bitvector32Term),
    Condition(ConditionTerm),
    FloatCondition {
        condition: CFloatCondition,
        is_float64: bool,
    },
    LeaveRegisteredLoad(Variable),
}

fn write_havoc_string(identity: &mut String, tag: &str, value: &str) {
    let _ = write!(identity, "{tag}{}:", value.len());
    identity.push_str(value);
}

fn write_havoc_block(identity: &mut String, block: PointerBlock) {
    match block {
        PointerBlock::PureFunctionApplication(application) => {
            let _ = write!(identity, "bpure{};", application.id());
        }
        PointerBlock::Concrete(name) => write_havoc_string(identity, "bc", &name),
        PointerBlock::StringLiteral {
            identity: name,
            bytes,
        } => {
            write_havoc_string(identity, "bsl", &name);
            let _ = write!(identity, "{}:", bytes.len());
            for byte in bytes {
                let _ = write!(identity, "{byte:02x}");
            }
            identity.push(';');
        }
        PointerBlock::Function(name) => write_havoc_string(identity, "bf", &name),
        PointerBlock::FunctionSymbolic(variable) => {
            let _ = write!(identity, "bfs{};", variable.0);
        }
        PointerBlock::ExternalArgument => identity.push_str("be;"),
        PointerBlock::ExternalObject(variable) => {
            let _ = write!(identity, "beo{};", variable.0);
        }
        PointerBlock::Symbolic(variable) => {
            let _ = write!(identity, "bs{};", variable.0);
        }
        PointerBlock::LoadedPointer(identity_id) => {
            let _ = write!(identity, "blp{};", identity_id.0);
        }
        PointerBlock::Heap(value) => {
            let _ = write!(identity, "bh{value};");
        }
        PointerBlock::Temporary(value) => {
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

fn push_havoc_binary(
    identity: &mut String,
    tasks: &mut Vec<HavocIdentityTask>,
    tag: &'static str,
    left: Bitvector32Term,
    right: Bitvector32Term,
) {
    identity.push_str(tag);
    identity.push('(');
    tasks.push(HavocIdentityTask::Text(")"));
    tasks.push(HavocIdentityTask::Bitvector(right));
    tasks.push(HavocIdentityTask::Text(","));
    tasks.push(HavocIdentityTask::Bitvector(left));
}

fn push_havoc_condition_binary(
    identity: &mut String,
    tasks: &mut Vec<HavocIdentityTask>,
    tag: &'static str,
    left: Bitvector32Term,
    right: Bitvector32Term,
) {
    push_havoc_binary(identity, tasks, tag, left, right);
}

fn havoc_range_identity(range: &CMemoryRange) -> String {
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
            HavocIdentityTask::Bitvector(Bitvector32Term::Constant(range.element_width())),
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
fn havoc_condition_identity(condition: &ConditionTerm, value: bool) -> String {
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
                write_havoc_block(&mut identity, pointer.block);
                identity.push(',');
                tasks.push(HavocIdentityTask::Text(")"));
                tasks.push(HavocIdentityTask::PointerOffset(pointer.offset));
            }
            HavocIdentityTask::PointerOffset(offset) => {
                crate::instrumentation::record_deterministic_work(1);
                match offset {
                    PointerOffsetTerm::Constant(value) => {
                        let _ = write!(identity, "oc{value};");
                    }
                    PointerOffsetTerm::Variable(variable) => {
                        if !push_registered_load(
                            &mut identity,
                            &mut tasks,
                            &mut active_loads,
                            variable,
                        ) {
                            let _ = write!(identity, "ov{};", variable.0);
                        }
                    }
                    PointerOffsetTerm::Add(left, right) => {
                        identity.push_str("oa(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::PointerOffset(*right));
                        tasks.push(HavocIdentityTask::Text(","));
                        tasks.push(HavocIdentityTask::PointerOffset(*left));
                    }
                    PointerOffsetTerm::Int32Scaled { value, byte_width }
                    | PointerOffsetTerm::Int64Scaled {
                        value, byte_width, ..
                    } => {
                        identity.push_str("os(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::PointerOffset(
                            PointerOffsetTerm::Constant(byte_width),
                        ));
                        tasks.push(HavocIdentityTask::Text(","));
                        tasks.push(HavocIdentityTask::Bitvector(*value));
                    }
                }
            }
            HavocIdentityTask::Bitvector(term) => {
                crate::instrumentation::record_deterministic_work(1);
                match term {
                    Bitvector32Term::MachineIntegerCast {
                        value,
                        source,
                        destination,
                    } => {
                        let _ = write!(identity, "tmcast{source:?}:{destination:?}(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Bitvector(*value));
                    }

                    Bitvector32Term::MachineIntegerConstant(value) => {
                        let _ = write!(identity, "twc{:?}:{:032x};", value.format(), value.bits());
                    }

                    Bitvector32Term::Constant(value) => {
                        let _ = write!(identity, "tc{value};");
                    }
                    Bitvector32Term::Int64Constant(value) => {
                        let _ = write!(identity, "ti64c{value};");
                    }
                    Bitvector32Term::UInt64Constant(value) => {
                        let _ = write!(identity, "tu64c{value};");
                    }
                    Bitvector32Term::Variable(variable) => {
                        if !push_registered_load(
                            &mut identity,
                            &mut tasks,
                            &mut active_loads,
                            variable,
                        ) {
                            let _ = write!(identity, "tv{};", variable.0);
                        }
                    }
                    Bitvector32Term::Add(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "ta", *left, *right)
                    }
                    Bitvector32Term::Subtract(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "ts", *left, *right)
                    }
                    Bitvector32Term::Multiply(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tm", *left, *right)
                    }
                    Bitvector32Term::Divide(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "td", *left, *right)
                    }
                    Bitvector32Term::UnsignedDivide(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tud", *left, *right)
                    }
                    Bitvector32Term::Remainder(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tr", *left, *right)
                    }
                    Bitvector32Term::UnsignedRemainder(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tur", *left, *right)
                    }
                    Bitvector32Term::ShiftLeft(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tl", *left, *right)
                    }
                    Bitvector32Term::ArithmeticShiftRight(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tar", *left, *right)
                    }
                    Bitvector32Term::LogicalShiftRight(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tlr", *left, *right)
                    }
                    Bitvector32Term::BitwiseAnd(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tba", *left, *right)
                    }
                    Bitvector32Term::BitwiseOr(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tbo", *left, *right)
                    }
                    Bitvector32Term::BitwiseXor(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tbx", *left, *right)
                    }
                    Bitvector32Term::BitwiseNot(value) => {
                        identity.push_str("tbn(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Bitvector(*value));
                    }
                    Bitvector32Term::Float32Negate(value) => {
                        identity.push_str("tf32n(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Bitvector(*value));
                    }
                    Bitvector32Term::Float64Negate(value) => {
                        identity.push_str("tf64n(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Bitvector(*value));
                    }
                    Bitvector32Term::Float32Binary {
                        operator,
                        left,
                        right,
                    } => {
                        let tag = match operator {
                            CFloatBinaryOperator::Add => "tf32a",
                            CFloatBinaryOperator::Subtract => "tf32s",
                            CFloatBinaryOperator::Multiply => "tf32m",
                            CFloatBinaryOperator::Divide => "tf32d",
                        };
                        push_havoc_binary(&mut identity, &mut tasks, tag, *left, *right);
                    }
                    Bitvector32Term::Float64Binary {
                        operator,
                        left,
                        right,
                    } => {
                        let tag = match operator {
                            CFloatBinaryOperator::Add => "tf64a",
                            CFloatBinaryOperator::Subtract => "tf64s",
                            CFloatBinaryOperator::Multiply => "tf64m",
                            CFloatBinaryOperator::Divide => "tf64d",
                        };
                        push_havoc_binary(&mut identity, &mut tasks, tag, *left, *right);
                    }
                    Bitvector32Term::Int64From32(value) => push_havoc_binary(
                        &mut identity,
                        &mut tasks,
                        "ti64f32",
                        *value.clone(),
                        *value,
                    ),
                    Bitvector32Term::UInt64From32(value) => push_havoc_binary(
                        &mut identity,
                        &mut tasks,
                        "tu64f32",
                        *value.clone(),
                        *value,
                    ),
                    Bitvector32Term::UInt32From64(value) => push_havoc_binary(
                        &mut identity,
                        &mut tasks,
                        "tu32f64",
                        *value.clone(),
                        *value,
                    ),
                    Bitvector32Term::Int64FromUInt32(value) => push_havoc_binary(
                        &mut identity,
                        &mut tasks,
                        "ti64fu32",
                        *value.clone(),
                        *value,
                    ),
                    Bitvector32Term::UInt64FromInt32(value) => push_havoc_binary(
                        &mut identity,
                        &mut tasks,
                        "tu64fi32",
                        *value.clone(),
                        *value,
                    ),
                    Bitvector32Term::UInt64FromInt64(value) => push_havoc_binary(
                        &mut identity,
                        &mut tasks,
                        "tu64fi64",
                        *value.clone(),
                        *value,
                    ),
                    Bitvector32Term::Int64BitwiseNot(value) => {
                        identity.push_str("ti64bn(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Bitvector(*value));
                    }
                    Bitvector32Term::UInt64BitwiseNot(value) => {
                        identity.push_str("tu64bn(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Bitvector(*value));
                    }
                    Bitvector32Term::Int64Add(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "ti64a", *left, *right)
                    }
                    Bitvector32Term::Int64Subtract(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "ti64s", *left, *right)
                    }
                    Bitvector32Term::Int64Multiply(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "ti64m", *left, *right)
                    }
                    Bitvector32Term::Int64Divide(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "ti64d", *left, *right)
                    }
                    Bitvector32Term::Int64Remainder(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "ti64r", *left, *right)
                    }
                    Bitvector32Term::Int64ShiftLeft(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "ti64l", *left, *right)
                    }
                    Bitvector32Term::Int64ArithmeticShiftRight(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "ti64ar", *left, *right)
                    }
                    Bitvector32Term::Int64BitwiseAnd(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "ti64ba", *left, *right)
                    }
                    Bitvector32Term::Int64BitwiseOr(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "ti64bo", *left, *right)
                    }
                    Bitvector32Term::Int64BitwiseXor(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "ti64bx", *left, *right)
                    }
                    Bitvector32Term::UInt64Add(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tu64a", *left, *right)
                    }
                    Bitvector32Term::UInt64Subtract(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tu64s", *left, *right)
                    }
                    Bitvector32Term::UInt64Multiply(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tu64m", *left, *right)
                    }
                    Bitvector32Term::UInt64Divide(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tu64d", *left, *right)
                    }
                    Bitvector32Term::UInt64Remainder(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tu64r", *left, *right)
                    }
                    Bitvector32Term::UInt64ShiftLeft(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tu64l", *left, *right)
                    }
                    Bitvector32Term::UInt64LogicalShiftRight(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tu64lr", *left, *right)
                    }
                    Bitvector32Term::UInt64BitwiseAnd(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tu64ba", *left, *right)
                    }
                    Bitvector32Term::UInt64BitwiseOr(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tu64bo", *left, *right)
                    }
                    Bitvector32Term::UInt64BitwiseXor(left, right) => {
                        push_havoc_binary(&mut identity, &mut tasks, "tu64bx", *left, *right)
                    }
                    Bitvector32Term::If {
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
                    Bitvector32Term::RangeFold {
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
                    Bitvector32Term::PureFunctionApplication { name, arguments } => {
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
                    Bitvector32Term::ClickFunctionApplication { .. }
                    | Bitvector32Term::AlgebraicMatch { .. }
                    | Bitvector32Term::IntegerToMachine { .. } => {
                        use std::hash::{Hash, Hasher};
                        let mut hasher = std::collections::hash_map::DefaultHasher::new();
                        term.hash(&mut hasher);
                        let _ = write!(identity, "click:{:x};", hasher.finish());
                    }
                    Bitvector32Term::MemoryLoad(_, pointer, kind) => {
                        let _ = write!(identity, "load:{kind:?}(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Pointer(*pointer));
                    }
                    Bitvector32Term::PointerAddress(pointer) => {
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
                    CFloatCondition::Comparison {
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
                    CFloatCondition::Classification {
                        classification,
                        value,
                    } => {
                        let _ = write!(identity, "fc{width}class{classification:?}(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Bitvector(*value));
                    }
                }
            }
            HavocIdentityTask::Condition(condition) => {
                crate::instrumentation::record_deterministic_work(1);
                match condition {
                    ConditionTerm::AlgebraicEqual(left, right) => {
                        let _ = write!(identity, "aeq({left:?},{right:?});");
                    }
                    ConditionTerm::Constant(value) => {
                        let _ = write!(identity, "cc{value};");
                    }
                    ConditionTerm::Variable(variable) => {
                        let _ = write!(identity, "cv{};", variable.0);
                    }
                    ConditionTerm::Bitvector32SignedLessThan(left, right) => {
                        push_havoc_condition_binary(&mut identity, &mut tasks, "clt", *left, *right)
                    }
                    ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
                        push_havoc_condition_binary(&mut identity, &mut tasks, "cle", *left, *right)
                    }
                    ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
                        push_havoc_condition_binary(&mut identity, &mut tasks, "cgt", *left, *right)
                    }
                    ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
                        push_havoc_condition_binary(&mut identity, &mut tasks, "cge", *left, *right)
                    }
                    ConditionTerm::Bitvector32Equal(left, right) => {
                        push_havoc_condition_binary(&mut identity, &mut tasks, "ceq", *left, *right)
                    }
                    ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
                        push_havoc_condition_binary(&mut identity, &mut tasks, "cao", *left, *right)
                    }
                    ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => {
                        push_havoc_condition_binary(&mut identity, &mut tasks, "cso", *left, *right)
                    }
                    ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right) => {
                        push_havoc_condition_binary(&mut identity, &mut tasks, "cmo", *left, *right)
                    }
                    ConditionTerm::Bitvector32SignedDivideOverflows(left, right) => {
                        push_havoc_condition_binary(&mut identity, &mut tasks, "cdo", *left, *right)
                    }
                    ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
                        push_havoc_condition_binary(&mut identity, &mut tasks, "clo", *left, *right)
                    }
                    ConditionTerm::Bitvector64SignedLessThan(left, right) => {
                        push_havoc_condition_binary(
                            &mut identity,
                            &mut tasks,
                            "ci64lt",
                            *left,
                            *right,
                        )
                    }
                    ConditionTerm::Bitvector64SignedLessEqual(left, right) => {
                        push_havoc_condition_binary(
                            &mut identity,
                            &mut tasks,
                            "ci64le",
                            *left,
                            *right,
                        )
                    }
                    ConditionTerm::Bitvector64SignedGreaterThan(left, right) => {
                        push_havoc_condition_binary(
                            &mut identity,
                            &mut tasks,
                            "ci64gt",
                            *left,
                            *right,
                        )
                    }
                    ConditionTerm::Bitvector64SignedGreaterEqual(left, right) => {
                        push_havoc_condition_binary(
                            &mut identity,
                            &mut tasks,
                            "ci64ge",
                            *left,
                            *right,
                        )
                    }
                    ConditionTerm::Bitvector64UnsignedLessThan(left, right) => {
                        push_havoc_condition_binary(
                            &mut identity,
                            &mut tasks,
                            "cu64lt",
                            *left,
                            *right,
                        )
                    }
                    ConditionTerm::Bitvector64UnsignedLessEqual(left, right) => {
                        push_havoc_condition_binary(
                            &mut identity,
                            &mut tasks,
                            "cu64le",
                            *left,
                            *right,
                        )
                    }
                    ConditionTerm::Bitvector64UnsignedGreaterThan(left, right) => {
                        push_havoc_condition_binary(
                            &mut identity,
                            &mut tasks,
                            "cu64gt",
                            *left,
                            *right,
                        )
                    }
                    ConditionTerm::Bitvector64UnsignedGreaterEqual(left, right) => {
                        push_havoc_condition_binary(
                            &mut identity,
                            &mut tasks,
                            "cu64ge",
                            *left,
                            *right,
                        )
                    }
                    ConditionTerm::Bitvector64Equal(left, right) => push_havoc_condition_binary(
                        &mut identity,
                        &mut tasks,
                        "c64eq",
                        *left,
                        *right,
                    ),
                    ConditionTerm::Bitvector64SignedAddOverflows(left, right) => {
                        push_havoc_condition_binary(
                            &mut identity,
                            &mut tasks,
                            "ci64ao",
                            *left,
                            *right,
                        )
                    }
                    ConditionTerm::Bitvector64SignedSubtractOverflows(left, right) => {
                        push_havoc_condition_binary(
                            &mut identity,
                            &mut tasks,
                            "ci64so",
                            *left,
                            *right,
                        )
                    }
                    ConditionTerm::Bitvector64SignedMultiplyOverflows(left, right) => {
                        push_havoc_condition_binary(
                            &mut identity,
                            &mut tasks,
                            "ci64mo",
                            *left,
                            *right,
                        )
                    }
                    ConditionTerm::Bitvector64SignedDivideOverflows(left, right) => {
                        push_havoc_condition_binary(
                            &mut identity,
                            &mut tasks,
                            "ci64do",
                            *left,
                            *right,
                        )
                    }
                    ConditionTerm::Bitvector64SignedShiftLeftOverflows(left, right) => {
                        push_havoc_condition_binary(
                            &mut identity,
                            &mut tasks,
                            "ci64lo",
                            *left,
                            *right,
                        )
                    }
                    crate::kernel::integer_comparison_condition!(_, _) => {
                        let _ = write!(identity, "icond{condition:?};");
                    }
                    ConditionTerm::Float32(condition) => {
                        tasks.push(HavocIdentityTask::FloatCondition {
                            condition,
                            is_float64: false,
                        });
                    }
                    ConditionTerm::Float64(condition) => {
                        tasks.push(HavocIdentityTask::FloatCondition {
                            condition,
                            is_float64: true,
                        });
                    }
                    ConditionTerm::PointerOffsetEqual(left, right) => {
                        identity.push_str("coe(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::PointerOffset(*right));
                        tasks.push(HavocIdentityTask::Text(","));
                        tasks.push(HavocIdentityTask::PointerOffset(*left));
                    }
                    ConditionTerm::PointerEqual(left, right) => {
                        identity.push_str("cpe(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Pointer(*right));
                        tasks.push(HavocIdentityTask::Text(","));
                        tasks.push(HavocIdentityTask::Pointer(*left));
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
        let block: PointerBlock = "local:borrowed-guard".into();
        let at = |offset| Pointer {
            block: block.clone(),
            offset: PointerOffsetTerm::Constant(offset),
        };
        let before = CMemory::new()
            .with_block(block.clone(), 16)
            .store(at(0), CValue::Int32(Bitvector32Term::Constant(7)))
            .store(at(8), CValue::Int32(Bitvector32Term::Constant(1)))
            .store(at(12), CValue::Int32(Bitvector32Term::Constant(9)));
        let range = CMemoryRange::new_with_element_width(at(8), 0u32.into(), 4u32.into(), 1);
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
            .store(at(8), CValue::Int32(Bitvector32Term::Constant(1)));
        assert!(!stale.matches_call_memory_havoc_result(
            &before,
            std::slice::from_ref(&range),
            &facts,
            None
        ));
    }

    #[test]
    fn call_havoc_preserves_only_existing_local_initialization() {
        let at = |offset| Pointer {
            block: "local:initialization".into(),
            offset: PointerOffsetTerm::Constant(offset),
        };
        let before = CMemory::new()
            .with_block(at(0).block.clone(), 16)
            .store(at(0), CValue::Int32(Bitvector32Term::Constant(7)));
        let range = CMemoryRange::new_with_element_width(at(0), 0u32.into(), 16u32.into(), 1);
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
            CValue::Int32(Bitvector32Term::Variable(Variable(944_016))),
        );
        assert!(
            named.known_value(&at(0)).is_none(),
            "logical naming does not materialize automatic storage"
        );
        assert!(named.has_initialized_bytes_at(&at(0), 4));
        let fresh = after
            .clone()
            .materialize_named_cell(at(8), CValue::Int32(Bitvector32Term::Constant(1)));
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
        let retired = after.without_local_block(&at(0).block);
        assert!(!retired.has_initialized_bytes_at(&at(0), 4));
        assert!(!retired.is_loadable_concretely(&at(0), 4));
    }

    #[test]
    fn local_initialization_havoc_checks_scale_with_changed_cells() {
        let target = Pointer {
            block: "local:target".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let range =
            CMemoryRange::new_with_element_width(target.clone(), 0u32.into(), 4u32.into(), 1);
        let facts = PureFactContext::new();
        let mut samples = Vec::new();
        for count in [16, 64, 256, 1024] {
            let mut before = CMemory::new()
                .with_block(target.block.clone(), 8)
                .store(target.clone(), CValue::Int32(Bitvector32Term::Constant(7)));
            for index in 0..count {
                let pointer = Pointer {
                    block: format!("local:ambient-{index}").into(),
                    offset: PointerOffsetTerm::Constant(0),
                };
                std::sync::Arc::make_mut(&mut before.heap)
                    .initialized
                    .record(&pointer, 4);
            }
            let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
                let after = before.clone().with_call_memory_havoc(
                    Variable(944_017),
                    std::slice::from_ref(&range),
                    &facts,
                    None,
                );
                after.matches_call_memory_havoc_result(
                    &before,
                    std::slice::from_ref(&range),
                    &facts,
                    None,
                )
            });
            assert!(checked);
            samples.push(work);
        }
        assert!(
            samples.iter().all(|work| *work <= samples[0] * 4 + 128),
            "ambient initialization scan: {samples:?}"
        );
    }

    #[test]
    fn call_havoc_drops_explicitly_written_local_union_views() {
        let pointer = Pointer {
            block: "local:borrowed-union".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before = CMemory::new()
            .with_block(pointer.block.clone(), 8)
            .store_union_views(
                pointer.clone(),
                8,
                vec![(
                    pointer.clone(),
                    CType::Int32,
                    CValue::Int32(Bitvector32Term::Constant(1)),
                )],
            );
        let range =
            CMemoryRange::new_with_element_width(pointer.clone(), 0u32.into(), 4u32.into(), 1);
        let facts = PureFactContext::new();
        let after = before.clone().with_call_memory_havoc(
            Variable(944_013),
            std::slice::from_ref(&range),
            &facts,
            None,
        );
        assert_eq!(after.known_union_value(&pointer, CType::Int32), None);
        assert!(after.matches_call_memory_havoc_result(
            &before,
            std::slice::from_ref(&range),
            &facts,
            None
        ));
    }

    #[test]
    fn call_havoc_drops_a_local_cell_written_through_an_interior_alias() {
        let pointer = Pointer {
            block: "local:interior-field".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let alias = Pointer::symbolic(Variable(944_021));
        let before = CMemory::new()
            .with_block(pointer.block.clone(), 4)
            .store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(7)));
        let facts = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(alias.clone(), pointer.offset_by_bytes(1)),
            true,
        );
        let range = CMemoryRange::new_with_element_width(alias, 0u32.into(), 1u32.into(), 1);
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
                .store(pointer, CValue::Int32(Bitvector32Term::Constant(7)))
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
        let local = Pointer {
            block: PointerBlock::Concrete("local:t".to_string()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let symbolic = Pointer {
            block: PointerBlock::Symbolic(Variable(944_001)),
            offset: PointerOffsetTerm::Constant(0),
        };
        let assumed_alias_range = CMemoryRange::new(
            symbolic.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        );
        let assumptions = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(symbolic, local.clone()),
            true,
        ));
        let unrelated_range = CMemoryRange::new(
            Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Constant(0),
            },
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        );
        let value = CValue::Int32(Bitvector32Term::Constant(41));
        let before = CMemory::new()
            .with_block(local.block.clone(), 4)
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
}

#[cfg(test)]
mod call_havoc_union_view_tests {
    use super::*;

    /// A call havoc drops a typed union view inside its write set exactly as
    /// it drops a cell, keeps one it cannot reach, and its checker accepts
    /// that result and refuses the one that keeps the written view.
    #[test]
    fn call_havoc_drops_union_views_in_its_write_set_and_the_checker_agrees() {
        let block: PointerBlock = "global:union-havoc".into();
        let written = Pointer {
            block: block.clone(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let sibling = Pointer {
            block: block.clone(),
            offset: PointerOffsetTerm::Constant(8),
        };
        let view = |pointer: &Pointer, value: u32| {
            (
                pointer.clone(),
                CType::Int32,
                CValue::Int32(Bitvector32Term::Constant(value)),
            )
        };
        let before = CMemory::new()
            .with_block(block, 16)
            .store_union_views(written.clone(), 8, vec![view(&written, 3)])
            .store_union_views(sibling.clone(), 8, vec![view(&sibling, 5)]);
        let range = CMemoryRange::new_with_element_width(
            written.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(4),
            1,
        );
        let assumptions = PureFactContext::new();
        let after = before.clone().with_call_memory_havoc(
            Variable(944_020),
            std::slice::from_ref(&range),
            &assumptions,
            None,
        );
        assert_eq!(after.known_union_value(&written, CType::Int32), None);
        assert_eq!(
            after.known_union_value(&sibling, CType::Int32),
            Some(CValue::Int32(Bitvector32Term::Constant(5)))
        );
        assert!(after.matches_call_memory_havoc_result(
            &before,
            std::slice::from_ref(&range),
            &assumptions,
            None,
        ));

        let mut stale = after.clone();
        std::sync::Arc::make_mut(&mut stale.union_cells).insert(
            (written.clone(), CType::Int32),
            CValue::Int32(Bitvector32Term::Constant(3)),
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

    fn int32_view(pointer: &Pointer, value: u32) -> (Pointer, CType, CValue) {
        (
            pointer.clone(),
            CType::Int32,
            CValue::Int32(Bitvector32Term::Constant(value)),
        )
    }

    fn zeroed_heap_with_cell() -> (CMemory, Pointer) {
        let base = Pointer {
            block: PointerBlock::Heap(944_100),
            offset: PointerOffsetTerm::Constant(0),
        };
        let mut memory = CMemory::new().with_block(base.block.clone(), 8);
        let heap = std::sync::Arc::make_mut(&mut memory.heap);
        heap.live_allocations
            .insert(base.clone(), Bitvector32Term::Constant(8));
        heap.zeroed_allocations.insert(base.clone());
        let memory = memory.store(base.clone(), int32(9));
        (memory, base)
    }

    /// The loop head forgets a typed union view exactly as it forgets a
    /// cell, unless the view's storage is preserved.
    #[test]
    fn loop_havoc_drops_union_views_outside_preserved_blocks() {
        let written = Pointer {
            block: "global:loop-union".into(),
            offset: PointerOffsetTerm::Constant(4),
        };
        let preserved = Pointer {
            block: "local:loop-union-kept".into(),
            offset: PointerOffsetTerm::Constant(4),
        };
        let before = CMemory::new()
            .with_block(written.block.clone(), 12)
            .with_block(preserved.block.clone(), 12)
            .store_union_views(written.clone(), 8, vec![int32_view(&written, 3)])
            .store_union_views(preserved.clone(), 8, vec![int32_view(&preserved, 5)]);
        let after = before.with_loop_memory_havoc_preserving_loans(
            Variable(944_101),
            &BTreeSet::from([preserved.block.clone()]),
            None,
            None,
        );
        assert_eq!(after.known_union_value(&written, CType::Int32), None);
        assert_eq!(
            after.known_union_value(&preserved, CType::Int32),
            Some(CValue::Int32(Bitvector32Term::Constant(5)))
        );
    }

    /// A zero reading answers for the bytes no cell covers, so the loop
    /// head that forgets a cell written over the zeros forgets the reading
    /// too: otherwise the load after the loop reads zero, not the value.
    #[test]
    fn loop_havoc_drops_the_zero_reading_under_a_forgotten_cell() {
        let (before, base) = zeroed_heap_with_cell();
        let beside = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::Constant(4),
        };
        // The cell covers the first four bytes, so only the bytes beside it
        // read as zero.
        assert!(!before.is_zeroed_heap_address(&base, 4, &PureFactContext::new()));
        assert!(before.is_zeroed_heap_address(&beside, 4, &PureFactContext::new()));
        let after = before.with_loop_memory_havoc_preserving_loans(
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
        let base = Pointer {
            block: PointerBlock::Heap(944_104),
            offset: PointerOffsetTerm::Constant(0),
        };
        let at = |offset: i64| Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::Constant(offset),
        };
        let mut memory = CMemory::new().with_block(base.block.clone(), 16);
        let heap = std::sync::Arc::make_mut(&mut memory.heap);
        heap.live_allocations
            .insert(base.clone(), Bitvector32Term::Constant(16));
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
            CValue::Int64(Bitvector32Term::Int64Constant(1 << 40)),
        );
        assert!(!wide.is_zeroed_heap_address(&at(4), 4, &facts));
        assert!(wide.is_zeroed_heap_address(&at(8), 4, &facts));
        // A symbolic offset into a block that holds a cell is not separated
        // from it by any constant.
        let symbolic = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::Variable(Variable(944_105))),
                byte_width: 4,
            },
        };
        assert!(memory.is_zeroed_heap_address(&symbolic, 4, &facts));
        assert!(!narrow.is_zeroed_heap_address(&symbolic, 4, &facts));
    }

    /// An interface join whose arms agree on a zero reading still drops it
    /// when one arm caches a value written over the zeros, and both arms'
    /// abstractions agree on that.
    #[test]
    fn interface_join_drops_a_zero_reading_one_arm_wrote_over() {
        let (wrote, base) = zeroed_heap_with_cell();
        let mut untouched = CMemory::new().with_block(base.block.clone(), 8);
        let heap = std::sync::Arc::make_mut(&mut untouched.heap);
        heap.live_allocations
            .insert(base.clone(), Bitvector32Term::Constant(8));
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
        let beside = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::Constant(4),
        };
        assert!(!from_wrote.is_zeroed_heap_address(&beside, 4, &PureFactContext::new()));
        assert_eq!(from_wrote.heap, from_untouched.heap);
    }
}

#[cfg(test)]
mod havoc_identity_tests {
    use super::*;

    fn nested_term(depth: usize, tail: u32) -> Bitvector32Term {
        (0..depth).fold(Bitvector32Term::Constant(tail), |term, _| {
            Bitvector32Term::Add(Box::new(Bitvector32Term::Constant(0)), Box::new(term))
        })
    }

    fn range(depth: usize, tail: u32) -> CMemoryRange {
        CMemoryRange::new(
            Pointer {
                block: "deep-havoc-range".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            nested_term(depth, tail),
            Bitvector32Term::Constant(1_024),
        )
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

        let before = CMemory::new().with_block("deep-havoc-range", 4_096);
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

    #[test]
    fn havoc_write_set_identity_scales_near_linearly_with_term_size() {
        let samples = [32, 64, 128, 256]
            .into_iter()
            .map(|depth| {
                let range = range(depth, 1);
                let (identity, work) = crate::instrumentation::measure_deterministic_work(|| {
                    memory_havoc_write_set_identity(std::slice::from_ref(&range))
                });
                assert!(!identity.is_empty());
                assert!(work > 0);
                (depth, work)
            })
            .collect::<Vec<_>>();
        assert!(
            samples
                .windows(2)
                .all(|pair| pair[1].1 <= pair[0].1.saturating_mul(3)),
            "havoc identity work grew faster than near-linearly: {samples:?}"
        );
    }
}

fn memory_havoc_write_set_fingerprint(mutable_ranges: &[CMemoryRange]) -> u32 {
    use std::hash::{Hash, Hasher};

    // This compact marker fingerprint remains form-invariant across proof
    // execution and independent certification. Call havocs supplement it with
    // a lossless structural key below; loop markers retain this shape because
    // their checked write set is already carried by the derivation edge.
    let mut shape = mutable_ranges
        .iter()
        .map(|range| {
            (
                format!("{:?}", range.base().block),
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

/// Whether a held resource grants read authority over a symbolic byte extent
/// at `base`.
///
/// The trusted graph/index selects a sole footprint or start supplier. The
/// ordinary read-core coverage judgment converts byte and element coordinates
/// and checks quantity and bounds. Unknown or ambiguous selection refuses;
/// this consumer must never search the resource input for a successful check.
pub(crate) fn resource_context_has_symbolic_range_read(
    resources: &ResourceContext,
    base: &Pointer,
    bytes: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    let footprint =
        CMemoryRange::new_with_element_width(base.clone(), 0u32.into(), bytes.clone(), 1);
    resources
        .symbolic_range_read_supported(&footprint, assumptions, None)
        .unwrap_or(false)
}

impl CLocalEnvironment {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with(mut self, name: impl Into<String>, value: CValue) -> Self {
        self.set(name, value);
        self
    }

    pub fn set(&mut self, name: impl Into<String>, value: CValue) {
        let c_type = value.c_type();
        self.set_typed(name, value, c_type);
    }

    pub fn set_typed(&mut self, name: impl Into<String>, value: CValue, c_type: CType) {
        self.set_typed_with_qualifiers(name, value, c_type, false, false);
    }

    /// Bind model data independently of any same-named automatic object.
    pub(in crate::kernel) fn bind_logical_typed(
        &mut self,
        name: impl Into<String>,
        value: CValue,
        c_type: CType,
    ) {
        let name = name.into();
        self.set_typed(name.clone(), value, c_type);
        let mut binding = self
            .bindings
            .get(&name)
            .expect("new logical binding")
            .clone();
        if let CLocalBinding::Object {
            storage_declared, ..
        } = &mut binding
        {
            *storage_declared = false;
        }
        self.insert_binding(name, binding);
    }

    pub(in crate::kernel) fn set_typed_with_qualifiers(
        &mut self,
        name: impl Into<String>,
        value: CValue,
        c_type: CType,
        volatile: bool,
        pointee_volatile: bool,
    ) {
        self.set_typed_with_all_qualifiers(
            name,
            value,
            c_type,
            volatile,
            pointee_volatile,
            false,
            false,
        );
    }

    pub(in crate::kernel) fn set_typed_with_all_qualifiers(
        &mut self,
        name: impl Into<String>,
        value: CValue,
        c_type: CType,
        volatile: bool,
        pointee_volatile: bool,
        constant: bool,
        pointee_constant: bool,
    ) {
        let name = name.into();
        let slot = self
            .bindings
            .get(&name)
            .map(CLocalBinding::slot)
            .cloned()
            .unwrap_or_else(|| CMemory::local_pointer(&name));
        self.set_typed_qualified_with_all_qualifiers(
            name,
            value.retag_pointer(c_type),
            c_type,
            slot,
            volatile,
            pointee_volatile,
            constant,
            pointee_constant,
        );
    }

    pub(in crate::kernel) fn set_typed_qualified_with_all_qualifiers(
        &mut self,
        name: impl Into<String>,
        value: CValue,
        c_type: CType,
        slot: Pointer,
        volatile: bool,
        pointee_volatile: bool,
        constant: bool,
        pointee_constant: bool,
    ) {
        let name = name.into();
        let storage_declared = self.bindings.get(&name).is_some_and(|binding| {
            binding.slot() == &slot
                && matches!(
                    binding,
                    CLocalBinding::Object {
                        storage_declared: true,
                        ..
                    } | CLocalBinding::UninitializedObject { .. }
                )
        });
        self.insert_binding(
            name,
            CLocalBinding::Object {
                storage_declared,
                value: value
                    .with_pointer_pointee_volatile(pointee_volatile)
                    .with_pointer_pointee_constant(pointee_constant),
                c_type,
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
        name: impl Into<String>,
        c_type: CType,
        slot: Pointer,
        volatile: bool,
        pointee_volatile: bool,
        constant: bool,
        pointee_constant: bool,
    ) {
        self.insert_binding(
            name.into(),
            CLocalBinding::GlobalObject {
                c_type,
                slot,
                volatile,
                pointee_volatile,
                constant,
                pointee_constant,
            },
        );
    }

    pub(in crate::kernel) fn set_uninitialized_with_all_qualifiers(
        &mut self,
        name: impl Into<String>,
        c_type: CType,
        slot: Pointer,
        volatile: bool,
        pointee_volatile: bool,
        constant: bool,
        pointee_constant: bool,
    ) {
        self.insert_binding(
            name.into(),
            CLocalBinding::UninitializedObject {
                c_type,
                slot,
                volatile,
                pointee_volatile,
                constant,
                pointee_constant,
            },
        );
    }

    pub(in crate::kernel) fn set_array_object_at(
        &mut self,
        name: impl Into<String>,
        element_type: CType,
        length: u32,
        slot: Pointer,
    ) {
        self.set_array_object_at_with_constant(name, element_type, length, slot, false);
    }

    pub(in crate::kernel) fn set_array_object_at_with_constant(
        &mut self,
        name: impl Into<String>,
        element_type: CType,
        length: u32,
        slot: Pointer,
        constant: bool,
    ) {
        self.insert_binding(
            name.into(),
            CLocalBinding::ArrayObject {
                element_type,
                length,
                slot,
                constant,
            },
        );
    }

    pub(in crate::kernel) fn set_aggregate_object_at(
        &mut self,
        name: impl Into<String>,
        layout: CAggregateLayout,
        slot: Pointer,
    ) {
        self.set_aggregate_object_at_with_constant(name, layout, slot, false);
    }

    pub(in crate::kernel) fn set_aggregate_object_at_with_constant(
        &mut self,
        name: impl Into<String>,
        layout: CAggregateLayout,
        slot: Pointer,
        constant: bool,
    ) {
        self.insert_binding(
            name.into(),
            CLocalBinding::AggregateObject {
                layout,
                slot,
                constant,
            },
        );
    }

    pub fn get(&self, name: &str) -> Option<&CValue> {
        match self.bindings.get(name) {
            Some(CLocalBinding::Object { value, .. }) => Some(value),
            Some(CLocalBinding::UninitializedObject { .. })
            | Some(CLocalBinding::GlobalObject { .. })
            | Some(CLocalBinding::ArrayObject { .. })
            | Some(CLocalBinding::AggregateObject { .. })
            | None => None,
        }
    }

    /// Read one automatic array's metadata by name without scanning the frame.
    pub fn array_object_element_type(&self, name: &str) -> Option<CType> {
        match self.bindings.get(name) {
            Some(CLocalBinding::ArrayObject { element_type, .. }) => Some(*element_type),
            _ => None,
        }
    }

    /// Exact name membership, including arrays and uninitialized objects.
    /// Proof-local binders use this indexed query to reject shadowing without
    /// materializing or scanning the complete local environment.
    pub fn contains_name(&self, name: &str) -> bool {
        self.bindings.contains_key(name)
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
    pub fn is_uninitialized_object(&self, name: &str) -> bool {
        matches!(
            self.bindings.get(name),
            Some(CLocalBinding::UninitializedObject { .. })
        )
    }

    pub fn object_values(&self) -> impl Iterator<Item = (&str, &CValue)> {
        self.bindings
            .iter()
            .filter_map(|(name, binding)| match binding {
                CLocalBinding::Object { value, .. } => Some((name.as_str(), value)),
                CLocalBinding::UninitializedObject { .. }
                | CLocalBinding::GlobalObject { .. }
                | CLocalBinding::ArrayObject { .. }
                | CLocalBinding::AggregateObject { .. } => None,
            })
    }

    pub fn aggregate_object_values(
        &self,
    ) -> impl Iterator<Item = (&str, &CAggregateLayout, &Pointer)> + '_ {
        self.bindings
            .iter()
            .filter_map(|(name, binding)| match binding {
                CLocalBinding::AggregateObject { layout, slot, .. } => {
                    Some((name.as_str(), layout, slot))
                }
                CLocalBinding::Object { .. }
                | CLocalBinding::UninitializedObject { .. }
                | CLocalBinding::GlobalObject { .. }
                | CLocalBinding::ArrayObject { .. } => None,
            })
    }

    /// Read one local array's pointer and element type without scanning the frame.
    pub fn array_object_value(&self, name: &str) -> Option<(CValue, CType)> {
        let CLocalBinding::ArrayObject {
            element_type,
            slot,
            constant,
            ..
        } = self.bindings.get(name)?
        else {
            return None;
        };
        Some((
            CValue::typed_pointer_with_pointee_constant(
                slot.clone(),
                element_type
                    .pointer_to()
                    .expect("array element type has a pointer type"),
                *constant,
            ),
            *element_type,
        ))
    }

    pub fn array_object_values(&self) -> impl Iterator<Item = (&str, CValue, CType)> + '_ {
        self.bindings
            .iter()
            .filter_map(|(name, binding)| match binding {
                CLocalBinding::ArrayObject {
                    element_type,
                    slot,
                    constant,
                    ..
                } => Some((
                    name.as_str(),
                    CValue::typed_pointer_with_pointee_constant(
                        slot.clone(),
                        element_type
                            .pointer_to()
                            .expect("array element type must have a pointer type"),
                        *constant,
                    ),
                    *element_type,
                )),
                CLocalBinding::Object { .. }
                | CLocalBinding::UninitializedObject { .. }
                | CLocalBinding::GlobalObject { .. }
                | CLocalBinding::AggregateObject { .. } => None,
            })
    }

    pub(in crate::kernel) fn object_type(&self, name: &str) -> Option<CType> {
        match self.binding(name) {
            Some(CLocalBinding::Object { c_type, .. }) => Some(*c_type),
            Some(CLocalBinding::UninitializedObject { c_type, .. }) => Some(*c_type),
            Some(CLocalBinding::GlobalObject { c_type, .. }) => Some(*c_type),
            Some(CLocalBinding::ArrayObject { element_type, .. }) => Some(*element_type),
            None => None,
            Some(CLocalBinding::AggregateObject { .. }) => None,
        }
    }

    pub(crate) fn scalar_object_type(&self, name: &str) -> Option<CType> {
        match self.binding(name) {
            Some(CLocalBinding::Object { c_type, .. }) => Some(*c_type),
            Some(CLocalBinding::UninitializedObject { c_type, .. }) => Some(*c_type),
            Some(CLocalBinding::GlobalObject { .. }) => None,
            Some(CLocalBinding::ArrayObject { .. })
            | Some(CLocalBinding::AggregateObject { .. })
            | None => None,
        }
    }

    pub(in crate::kernel) fn binding(&self, name: &str) -> Option<&CLocalBinding> {
        self.bindings.get(name)
    }

    pub(in crate::kernel) fn slot(&self, name: &str) -> Option<&Pointer> {
        self.binding(name).map(CLocalBinding::slot)
    }

    pub(in crate::kernel) fn slots(&self) -> impl Iterator<Item = &Pointer> {
        self.slots.keys()
    }

    pub(in crate::kernel) fn name_for_slot(&self, pointer: &Pointer) -> Option<&str> {
        self.slots.get(pointer).map(String::as_str)
    }

    pub(in crate::kernel) fn is_array_object(&self, name: &str) -> bool {
        matches!(self.binding(name), Some(CLocalBinding::ArrayObject { .. }))
    }

    pub(in crate::kernel) fn is_global_object(&self, name: &str) -> bool {
        matches!(self.binding(name), Some(CLocalBinding::GlobalObject { .. }))
    }

    pub(in crate::kernel) fn is_aggregate_object(&self, name: &str) -> bool {
        matches!(
            self.binding(name),
            Some(CLocalBinding::AggregateObject { .. })
        )
    }

    pub(crate) fn aggregate_object_pointer(&self, name: &str) -> Option<&Pointer> {
        match self.binding(name) {
            Some(CLocalBinding::AggregateObject { slot, .. }) => Some(slot),
            _ => None,
        }
    }

    pub(crate) fn aggregate_layout(&self, name: &str) -> Option<&CAggregateLayout> {
        match self.binding(name) {
            Some(CLocalBinding::AggregateObject { layout, .. }) => Some(layout),
            _ => None,
        }
    }
}

impl CLocalBinding {
    pub(in crate::kernel) fn slot(&self) -> &Pointer {
        match self {
            Self::Object { slot, .. }
            | Self::UninitializedObject { slot, .. }
            | Self::GlobalObject { slot, .. }
            | Self::ArrayObject { slot, .. }
            | Self::AggregateObject { slot, .. } => slot,
        }
    }
}

impl CLocalEnvironment {
    fn insert_binding(&mut self, name: String, binding: CLocalBinding) {
        let slot = binding.slot().clone();
        let old_slot = self.bindings.get(&name).map(CLocalBinding::slot).cloned();
        std::sync::Arc::make_mut(&mut self.bindings).insert(name.clone(), binding);
        if let Some(old_slot) = old_slot
            && old_slot != slot
        {
            std::sync::Arc::make_mut(&mut self.slots).remove(&old_slot);
        }
        std::sync::Arc::make_mut(&mut self.slots).insert(slot, name);
    }

    /// Puts back a binding read from another environment with
    /// [`Self::binding`].
    pub(in crate::kernel) fn restore_binding(&mut self, name: &str, binding: CLocalBinding) {
        self.insert_binding(name.to_string(), binding);
    }

    /// Makes an initialized scalar object uninitialized again, keeping its
    /// slot, type and qualifiers, so a read of it is refused. Returns whether
    /// the name held such an object.
    pub(in crate::kernel) fn forget_initialization(&mut self, name: &str) -> bool {
        let Some(CLocalBinding::Object {
            c_type,
            slot,
            volatile,
            pointee_volatile,
            constant,
            pointee_constant,
            ..
        }) = self.bindings.get(name).cloned()
        else {
            return false;
        };
        self.insert_binding(
            name.to_string(),
            CLocalBinding::UninitializedObject {
                c_type,
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
    pub(in crate::kernel) fn remove(&mut self, name: &str) {
        let Some(binding) = std::sync::Arc::make_mut(&mut self.bindings).remove(name) else {
            return;
        };
        std::sync::Arc::make_mut(&mut self.slots).remove(binding.slot());
    }
}

impl CBlock {
    pub fn new(size: u32) -> Self {
        Self {
            size: Bitvector32Term::Constant(size),
            read_only: false,
            declared_object: None,
            explicit_scalar_ownership: false,
            uint32_representation: None,
        }
    }

    pub fn read_only(size: u32) -> Self {
        Self {
            size: Bitvector32Term::Constant(size),
            read_only: true,
            declared_object: None,
            explicit_scalar_ownership: false,
            uint32_representation: None,
        }
    }

    pub(in crate::kernel) fn with_symbolic_size(size: Bitvector32Term) -> Self {
        Self {
            size,
            read_only: false,
            declared_object: None,
            explicit_scalar_ownership: false,
            uint32_representation: None,
        }
    }

    pub fn size(&self) -> &Bitvector32Term {
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
fn call_havoc_candidates(mutable_ranges: &[CMemoryRange]) -> AliasCandidates {
    AliasCandidates::of_blocks(mutable_ranges.iter().map(|range| &range.base().block))
}

/// What a caller keeps owning across one call: the residual resource context
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
/// owns) covers: the havoc drops its cached value as it drops every candidate
/// cell, and records the member that holds it on the edge, which is what
/// names a later load of the cell across the call at its pre-call value.
/// Retaining the cached value in the map instead made every later load of the
/// block compare against more cached cells, and the arena pipeline's load
/// resolution then ran past its time limit. A residual *view* keeps nothing, since the callee may hold its
/// owner, and a residual instance that cannot be opened contributes nothing.
/// The body facts hold wherever the instance is held, which is here.
#[derive(Clone, Debug)]
pub(in crate::kernel) struct CallKeptOwnership {
    residual: ResourceContext,
    opened: CallKeptRanges,
    placement: Option<PureFactContext>,
}

/// The kept memory a call havoc records on its edge: owned ranges, and the
/// condition premises that place a cell in them. See
/// [`CMemoryDerivation::CallHavoc`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallKeptRanges {
    ranges: ResourceContext,
    premises: Vec<(ConditionTerm, bool)>,
}

impl CallKeptRanges {
    pub(in crate::kernel) fn new(
        ranges: ResourceContext,
        premises: Vec<(ConditionTerm, bool)>,
    ) -> Self {
        Self { ranges, premises }
    }

    fn is_empty(&self) -> bool {
        self.ranges.is_pristine_semantically_empty()
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
                    facts.assume_proposition(Proposition::ConditionIs(condition.clone(), *value))
                }),
        )
    }

    /// The kept memory recorded on the call havoc edge that derived `after`,
    /// if that edge is one: what a call's effect summary may keep beside its
    /// declared write set.
    pub(in crate::kernel) fn recorded_on(after: &CMemory) -> Option<Self> {
        let derivation = crate::kernel::intern_c_memory_ref(after).derivation()?;
        let CMemoryDerivation::CallHavoc {
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
        pointer: &Pointer,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        self.range_holding(assumptions, None, pointer, bytes)
            .is_some()
    }

    pub(in crate::kernel) fn contains_range(&self, range: &CMemoryRange) -> bool {
        self.ranges
            .contains_exact_representation(&CResourceFact::own_memory(range.clone()))
    }

    /// The kept range holding the access. `placement` is the premises already
    /// assumed into `assumptions`, when the caller has built it once.
    pub(in crate::kernel) fn range_holding<'a>(
        &'a self,
        assumptions: &PureFactContext,
        placement: Option<&PureFactContext>,
        pointer: &Pointer,
        bytes: u32,
    ) -> Option<&'a CMemoryRange> {
        match placement {
            Some(placement) => {
                placement.kept_range_holding_access(&self.ranges, || None, pointer, bytes)
            }
            None => assumptions.kept_range_holding_access(
                &self.ranges,
                || self.placement(assumptions),
                pointer,
                bytes,
            ),
        }
    }

    fn identity(&self) -> String {
        let ranges = self
            .ranges
            .facts()
            .iter()
            .filter_map(|fact| fact.memory_own_range().cloned())
            .collect::<Vec<_>>();
        let mut identity = memory_havoc_write_set_identity(&ranges);
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
    /// bodies. The write-set marker spells both, so a content-equal snapshot
    /// whose edge was recorded first carries the same ones.
    pub(in crate::kernel) fn recorded_on(
        after: &CMemory,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        let kept = CallKeptRanges::recorded_on(after)?;
        // This residual is permanently empty: recorded authority is carried
        // only by `kept`, not by facts inserted into this placeholder.
        Some(Self::new(ResourceContext::new(), kept, assumptions))
    }

    /// The owned member that holds every byte of the access, from the opened
    /// bodies or the residual's own flat members: one base-index lookup in
    /// each, never a scan.
    fn member_holding(
        &self,
        pointer: &Pointer,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> Option<CMemoryRange> {
        self.opened
            .range_holding(assumptions, self.placement.as_ref(), pointer, bytes)
            .or_else(|| assumptions.owned_member_holding_access(&self.residual, pointer, bytes))
            .cloned()
    }
}

/// How the call havoc rule treats one cell.
enum CallHavocCellRule {
    /// Kept by the separation rule, without the caller's ownership.
    Separate,
    /// Kept because this member of what the caller keeps owning holds it.
    KeptByCaller(CMemoryRange),
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
    pointer: &Pointer,
    value: &CValue,
    mutable_ranges: &[CMemoryRange],
    assumptions: &PureFactContext,
    kept: Option<&CallKeptOwnership>,
    preserve_local_slots: bool,
) -> CallHavocCellRule {
    if preserve_local_slots
        && pointer.block.starts_with("local:")
        // An opaque pointer may reach a local even when no exact alias has
        // yet been stated. Absence of an alias is not separation evidence.
        && mutable_ranges.iter().all(|range| !matches!(range.base().block, PointerBlock::Symbolic(_)))
        && !mutable_ranges.iter().any(|range| {
            range.base().block == pointer.block
                || assumptions
                    .equality_graph
                    .pointer_in_block(range.base(), &pointer.block)
                    .is_some()
        })
    {
        return if mutable_ranges.iter().all(|range| {
            range.base().block == pointer.block
                || !pointers_proven_equal_for_memory_resolution(range.base(), pointer, assumptions)
        }) {
            CallHavocCellRule::Separate
        } else {
            CallHavocCellRule::Dropped
        };
    }
    let bytes = crate::kernel::reasoning::cell_access_byte_width(value);
    if crate::kernel::memory_provenance::typed_ranges_disjoint_from_pointer_evidence(
        mutable_ranges,
        pointer,
        bytes,
        assumptions,
    )
    .is_some()
    {
        return CallHavocCellRule::Separate;
    }
    match kept.and_then(|kept| kept.member_holding(pointer, bytes, assumptions)) {
        Some(range) => CallHavocCellRule::KeptByCaller(range),
        None => CallHavocCellRule::Dropped,
    }
}

/// The ranges a call havoc records as kept by its caller: every opened
/// residual body range with the premises that place cells in them, every
/// flat owned member of the residual based in a block the write set may
/// alias, and each flat member that kept a cached cell. The edge carries them
/// so a later load of a cell they hold is named across the call, and the
/// write-set marker spells them so two paths that keep different memory
/// never share the resulting snapshot.
///
/// The flat members come from the caller's ownership, not from the cache: a
/// member whose cell an earlier call's havoc already dropped -- and which no
/// load has cached again since -- is recorded all the same, so a load after
/// this call is named across it
/// (`mdtests/call_keeps_an_uncached_flat_field_beside_folded_state.md`). A
/// member in a block proven distinct from every write-set base is not
/// recorded: the separation rule keeps its cells without it. The members are
/// read from the residual's per-block owned-memory index over
/// `candidates`, the same block ranges the havoc visits, so the cost is the
/// members that can alias the footprint, never the residual's other
/// resources. A write set that reaches unnamed memory sits in a symbolic
/// block, whose candidates are every block.
fn call_havoc_kept_ranges(
    kept: Option<&CallKeptOwnership>,
    flat_hits: Vec<CMemoryRange>,
    candidates: &AliasCandidates,
) -> Option<CallKeptRanges> {
    let kept = kept?;
    let mut ranges = kept.opened.ranges.clone();
    let mut recorded = ranges
        .facts()
        .iter()
        .filter_map(|fact| fact.memory_own_range().cloned())
        .collect::<BTreeSet<_>>();
    let residual_members = kept
        .residual
        .owned_memory_members_in_candidate_blocks(candidates);
    for range in flat_hits
        .into_iter()
        .chain(residual_members.into_iter().cloned())
    {
        if recorded.insert(range.clone()) {
            ranges = ranges.unchecked_with_fact(CResourceFact::own_memory(range));
        }
    }
    let recorded = CallKeptRanges::new(ranges, kept.opened.premises.clone());
    (!recorded.is_empty()).then_some(recorded)
}

fn call_write_set_marker(
    variable: u64,
    mutable_ranges: &[CMemoryRange],
    kept_ranges: Option<&CallKeptRanges>,
) -> PointerBlock {
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

/// Whether a havoc that preserves loans keeps the cell at this address: the
/// one rule, asked by the loop head and by the interface join.
///
/// Unlike a call havoc this is not a separation question at all. A loop body,
/// or the arm of a branch the join is merging, may write through any pointer
/// it can reach, so the only cells that survive are the ones something else
/// guarantees: storage the function declared and did not expose
/// (`preserved_blocks`), and bytes an active loan protects from being written
/// at all. That is why it consults the ledger rather than the assumptions, and
/// why the resource tracker's havoc arms cannot answer it.
///
/// A cell whose width is unknown fails closed, because keeping its value on a
/// loan the ledger would have permitted a write through is a promise nothing
/// proved (`docs/internals/stable-views.md`).
fn loan_preserving_havoc_keeps_cell(
    pointer: &Pointer,
    byte_width: u32,
    preserved_blocks: &BTreeSet<PointerBlock>,
    ledger: Option<&crate::kernel::loans::LoanLedger>,
) -> bool {
    preserved_blocks.contains(&pointer.block)
        || ledger.is_some_and(|ledger| {
            byte_width != 0
                && ledger
                    .permits_memory_access(&CMemoryRange::new_with_element_width(
                        pointer.clone(),
                        Bitvector32Term::Constant(0),
                        Bitvector32Term::Constant(byte_width),
                        1,
                    ))
                    .is_err()
        })
}

/// [`loan_preserving_havoc_keeps_cell`] for every slot of a run at once. A run
/// in a preserved block keeps every slot; outside one, a slot survives only
/// where a loan protects its bytes, so no loan over any of the run's bytes
/// keeps none. Anything else is asked slot by slot. The run's slots hold no
/// typed union views (a run is never seeded beside them), so each slot's
/// width is its value's.
fn loan_preserving_havoc_keeps_run(
    run: &CellRun,
    preserved_blocks: &BTreeSet<PointerBlock>,
    ledger: Option<&crate::kernel::loans::LoanLedger>,
) -> (SlotSet, crate::kernel::primitives::RuleAnswer) {
    let exact = crate::kernel::primitives::RuleAnswer::Exact;
    if preserved_blocks.contains(&run.base().block) {
        return (SlotSet::All, exact);
    }
    let Some(ledger) = ledger else {
        return (SlotSet::Nothing, exact);
    };
    let whole = CMemoryRange::new_with_element_width(
        run.base().clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(
            (run.count().saturating_sub(1))
                .saturating_mul(run.element_width())
                .saturating_add(run.value_width()),
        ),
        1,
    );
    if ledger.permits_memory_access(&whole).is_ok() {
        (SlotSet::Nothing, exact)
    } else {
        (SlotSet::PerSlot, exact)
    }
}

/// The union of the arms' maps, built from the first arm's by the entries
/// another arm adds to it. An entry two arms hold with different values is
/// returned as the error. Only the entries on which an arm differs from the
/// first are visited.
fn union_of_arm_maps<'a, K, V>(
    first: &SnapshotMap<K, V>,
    others: impl Iterator<Item = &'a SnapshotMap<K, V>>,
) -> Result<SnapshotMap<K, V>, K>
where
    K: Ord + Clone + std::hash::Hash + 'a,
    V: Clone + PartialEq + std::hash::Hash + 'a,
{
    let mut union = first.clone();
    for other in others {
        for change in first.diff(other) {
            match change {
                SnapshotMapChange::Removed(_) => {}
                SnapshotMapChange::Changed(key) => return Err(key.clone()),
                SnapshotMapChange::Added(key) => {
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
    first: &SnapshotSet<K>,
    others: impl Iterator<Item = &'a SnapshotSet<K>>,
) -> SnapshotSet<K>
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

/// The widest typed overlay recorded at each address, so that the loan
/// question above covers every byte the cell can be read as.
fn union_overlay_widths(memory: &CMemory) -> BTreeMap<Pointer, u32> {
    let mut widths = BTreeMap::<Pointer, u32>::new();
    for (pointer, c_type) in memory.union_cells.keys() {
        widths
            .entry(pointer.clone())
            .and_modify(|width| *width = (*width).max(c_type.byte_width()))
            .or_insert_with(|| c_type.byte_width());
    }
    widths
}

/// Whether a heap allocation's recorded entry (its base) may contain
/// `pointer`.
///
/// The deciding rule is the equality invariant: differently spelled pointer
/// blocks are not separate unless [`PointerBlock::proven_distinct`] or the
/// assumptions say so, so two edges control every answer. Entries whose block
/// is proven distinct from the query pointer's never contain it. Entries in a
/// block merely spelled differently do, once an assumed pointer equality names
/// one address under the two spellings; a tried interior-with-offset alias is
/// answered `false` here, which is conservative — the free-retirement path
/// clears whole aliased-spelling blocks itself, so no stale cached cell or
/// zeroed status survives under an alias spelling.
fn heap_allocation_may_contain_pointer(
    base: &Pointer,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    if base != pointer && base.block.proven_distinct(&pointer.block) {
        return false;
    }
    if base.block != pointer.block {
        return base.offset == pointer.offset
            && pointers_proven_equal_for_memory_resolution(base, pointer, assumptions);
    }
    if base.block != PointerBlock::ExternalArgument {
        return true;
    }

    if pointer.offset == base.offset {
        return true;
    }

    fn contains_base_offset(term: &PointerOffsetTerm, base: &PointerOffsetTerm) -> bool {
        match term {
            PointerOffsetTerm::Add(left, right) => {
                left.as_ref() == base
                    || right.as_ref() == base
                    || contains_base_offset(left, base)
                    || contains_base_offset(right, base)
            }
            PointerOffsetTerm::Constant(_)
            | PointerOffsetTerm::Variable(_)
            | PointerOffsetTerm::Int32Scaled { .. }
            | PointerOffsetTerm::Int64Scaled { .. } => false,
        }
    }

    contains_base_offset(&pointer.offset, &base.offset)
}

/// The one snapshot a pure-function pointer argument is anchored to when the
/// callee provably reads no memory.
///
/// Such a function is a function of its argument values, so the ambient
/// snapshot in the argument term is dead weight — and live weight would be
/// worse than dead: it makes the same proposition a different term on either
/// side of any C write, which is what stopped a `fold` from discharging a
/// body fact applying a pure predicate to a pointer. The snapshot is empty, so
/// nothing can be read through it by construction, and it is cached per thread
/// so repeated uses share one storage root.
pub fn value_independent_click_memory() -> CMemory {
    thread_local! {
        static CANONICAL: CMemory = CMemory::new();
    }
    CANONICAL.with(Clone::clone)
}

impl CMemory {
    pub fn new() -> Self {
        Self::default()
    }

    pub(crate) fn has_same_snapshot_markers(&self, other: &Self) -> bool {
        self.blocks == other.blocks
            && self.forgotten.ended_local_blocks == other.forgotten.ended_local_blocks
            && self.heap == other.heap
    }

    pub fn with_block(mut self, block: impl Into<PointerBlock>, size: u32) -> Self {
        let block = block.into();
        // Havoc marker blocks mean "the state may have changed", never "a
        // fresh block appeared"; recording a benign block-declaration edge
        // for one would launder the havoc (conventions.md's soundness trap,
        // pinned by `conditions_equal_modulo_proven_snapshots_needs_frame_
        // evidence`). The havoc producers insert their markers directly,
        // but tests and any future caller may write them through this
        // constructor, so the refusal lives here.
        if block.starts_with("havoc:") || block.starts_with("call-havoc:") {
            let diagnostic_base = self.clone();
            std::sync::Arc::make_mut(&mut self.blocks).insert(block.clone(), CBlock::new(size));
            self.record_diagnostic_transform(
                "insert havoc marker",
                vec![diagnostic_base],
                vec![CValue::pointer(Pointer {
                    block,
                    offset: PointerOffsetTerm::Constant(0),
                })],
            );
            return self;
        }
        let base = intern_derivation_base(&mut self);
        std::sync::Arc::make_mut(&mut self.blocks).insert(block.clone(), CBlock::new(size));
        record_c_memory_derivation(&mut self, CMemoryDerivation::BlockDeclared { base, block });
        self
    }

    /// Declared automatic scalars use allocation ownership, never the legacy
    /// implicit local access rule. One block lookup is independent of other cells.
    pub(in crate::kernel) fn requires_explicit_scalar_ownership(&self, pointer: &Pointer) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        self.blocks
            .get(&pointer.block)
            .is_some_and(|block| block.explicit_scalar_ownership)
    }

    /// Retains a complete declaration separately from its allocation extent,
    /// values, initialization and authority. Only actual declaration producers
    /// call this; a raw block or footprint does not establish an object.
    fn with_complete_declaration(
        mut self,
        block: PointerBlock,
        size: u32,
        declared_object: CDeclaredObject,
        read_only: bool,
        explicit_scalar_ownership: bool,
        uint32_representation: Option<UInt32RepresentationProfile>,
    ) -> Self {
        let mut declaration = CBlock::new(size);
        declaration.declared_object = Some(declared_object);
        declaration.read_only = read_only;
        declaration.explicit_scalar_ownership = explicit_scalar_ownership;
        declaration.uint32_representation = uint32_representation;
        if self.blocks.get(&block) == Some(&declaration) {
            return self;
        }
        let base = intern_derivation_base(&mut self);
        Arc::make_mut(&mut self.blocks).insert(block.clone(), declaration);
        record_c_memory_derivation(&mut self, CMemoryDerivation::BlockDeclared { base, block });
        self
    }

    #[cfg(test)]
    pub(in crate::kernel) fn with_declared_scalar_block(
        self,
        block: PointerBlock,
        size: u32,
        c_type: CType,
    ) -> Self {
        self.with_declared_scalar_block_in_target(block, size, c_type, None)
    }

    pub(in crate::kernel) fn with_declared_scalar_block_in_target(
        self,
        block: PointerBlock,
        size: u32,
        c_type: CType,
        byte_order: Option<ByteOrder>,
    ) -> Self {
        let profile =
            (c_type == CType::UInt32 && size == 4 && byte_order == Some(ByteOrder::Little))
                .then_some(UInt32RepresentationProfile::LittleEndian);
        self.with_complete_declaration(
            block,
            size,
            CDeclaredObject::Scalar(c_type),
            false,
            true,
            profile,
        )
    }

    pub(in crate::kernel) fn declared_uint32_representation(
        &self,
        pointer: &Pointer,
    ) -> Option<UInt32RepresentationProfile> {
        if pointer.offset.as_const() != Some(0)
            || pointer.is_in_null_block()
            || self.is_ended_local_address(pointer)
            || self.is_deallocated_heap_address(pointer, &PureFactContext::new())
        {
            return None;
        }
        crate::instrumentation::record_deterministic_work(1);
        let block = self.blocks.get(&pointer.block)?;
        if block.size.as_const() != Some(4)
            || !matches!(
                block.declared_object,
                Some(CDeclaredObject::Scalar(CType::UInt32))
            )
        {
            return None;
        }
        block.uint32_representation
    }

    pub(in crate::kernel) fn with_declared_scalar_block_or_read_only(
        self,
        block: PointerBlock,
        size: u32,
        c_type: CType,
        read_only: bool,
    ) -> Self {
        self.with_complete_declaration(
            block,
            size,
            CDeclaredObject::Scalar(c_type),
            read_only,
            false,
            None,
        )
    }

    pub(in crate::kernel) fn with_declared_aggregate_block(
        self,
        block: PointerBlock,
        layout: &CAggregateLayout,
    ) -> Self {
        self.with_declared_aggregate_block_or_read_only(block, layout, false)
    }

    pub(in crate::kernel) fn with_declared_aggregate_block_or_read_only(
        self,
        block: PointerBlock,
        layout: &CAggregateLayout,
        read_only: bool,
    ) -> Self {
        self.with_complete_declaration(
            block,
            layout.size_bytes(),
            CDeclaredObject::Aggregate(Arc::new(layout.clone())),
            read_only,
            false,
            None,
        )
    }

    pub(in crate::kernel) fn with_declared_array_block(
        self,
        block: PointerBlock,
        element_type: CType,
        count: u32,
    ) -> Option<Self> {
        self.with_declared_array_block_or_read_only(block, element_type, count, false)
    }

    pub(in crate::kernel) fn with_declared_array_block_or_read_only(
        self,
        block: PointerBlock,
        element_type: CType,
        count: u32,
        read_only: bool,
    ) -> Option<Self> {
        let width = element_type.byte_width();
        if width == 0 {
            return None;
        }
        let size = count.checked_mul(width)?;
        let shape = self.blocks.get(&block).and_then(|declaration| {
            match declaration.declared_object.as_ref() {
                Some(CDeclaredObject::Array {
                    element_type: held,
                    count: held_count,
                    shape,
                }) if *held == element_type && *held_count == count => shape.clone(),
                _ => None,
            }
        });
        Some(self.with_complete_declaration(
            block,
            size,
            CDeclaredObject::Array {
                element_type,
                count,
                shape,
            },
            read_only,
            false,
            None,
        ))
    }

    /// Attach dimensions only to an actual scalar-array declaration. Byte
    /// blocks, raw construction markers and ownership ranges cannot issue them.
    pub(in crate::kernel) fn with_declared_array_shape(
        mut self,
        block: &PointerBlock,
        element: CType,
        count: u32,
        shape: &[u32],
    ) -> Option<Self> {
        checked_scalar_array_shape(element, count, shape)?;
        let declaration = self.blocks.get(block)?;
        if !matches!(declaration.declared_object.as_ref(),
            Some(CDeclaredObject::Array { element_type, count: held, shape: old })
            if *element_type == element && *held == count
                && old.as_deref().is_none_or(|old| old == shape))
        {
            return None;
        }
        let base = intern_derivation_base(&mut self);
        let mut declaration = self.blocks.get(block)?.clone();
        declaration.declared_object = Some(CDeclaredObject::Array {
            element_type: element,
            count,
            shape: (shape.len() > 1).then(|| Arc::from(shape)),
        });
        Arc::make_mut(&mut self.blocks).insert(block.clone(), declaration);
        record_c_memory_derivation(
            &mut self,
            CMemoryDerivation::BlockDeclared {
                base,
                block: block.clone(),
            },
        );
        Some(self)
    }

    /// Complete scalar construction without changing its extent, type, cells,
    /// ownership, or allocation generation. Checked declaration execution is
    /// the only caller; later alias writes see the block's read-only status.
    pub(in crate::kernel) fn freeze_declared_scalar(mut self, block: &PointerBlock) -> Self {
        let base = intern_derivation_base(&mut self);
        let mut declaration = self
            .blocks
            .get(block)
            .expect("freshly allocated scalar block")
            .clone();
        assert!(matches!(
            declaration.declared_object,
            Some(CDeclaredObject::Scalar(_))
        ));
        declaration.read_only = true;
        std::sync::Arc::make_mut(&mut self.blocks).insert(block.clone(), declaration);
        record_c_memory_derivation(
            &mut self,
            CMemoryDerivation::BlockDeclared {
                base,
                block: block.clone(),
            },
        );
        self
    }

    /// Describe initially unwritten complete-object storage. This builds a
    /// proof-entry snapshot, not an allocation transition or lifetime reset:
    /// existing writes remain recorded, a symbolic identity can still alias
    /// arguments, and no memory-DAG transport edge is granted.
    pub fn with_uninitialized_block(mut self, block: impl Into<PointerBlock>, size: u32) -> Self {
        let diagnostic_base = self.clone();
        let block = block.into();
        std::sync::Arc::make_mut(&mut self.blocks).insert(block.clone(), CBlock::new(size));
        self.record_diagnostic_transform(
            "declare uninitialized block",
            vec![diagnostic_base],
            vec![
                CValue::pointer(Pointer {
                    block: block.clone(),
                    offset: PointerOffsetTerm::Constant(0),
                }),
                CValue::Int32(size.into()),
            ],
        );
        self.with_uninitialized_object(
            Pointer {
                block,
                offset: PointerOffsetTerm::Constant(0),
            },
            size,
        )
    }

    /// Record an unwritten object footprint without declaring or resizing its
    /// containing allocation. Proof-entry ownership supplies its storage
    /// authority and liveness separately; this marker supplies neither.
    pub fn with_uninitialized_object(mut self, pointer: Pointer, size: u32) -> Self {
        let diagnostic_base = self.clone();
        std::sync::Arc::make_mut(&mut self.heap)
            .uninitialized_objects
            .insert(pointer.clone(), size);
        self.record_diagnostic_transform(
            "mark uninitialized object",
            vec![diagnostic_base],
            vec![CValue::pointer(pointer.clone()), CValue::Int32(size.into())],
        );
        self
    }

    pub(crate) fn has_uninitialized_object_footprints(&self) -> bool {
        !self.heap.uninitialized_objects.is_empty()
    }

    /// The native entry rule may assume a scalar object only at the exact
    /// domain selected by its interface. This creates neither storage nor a
    /// readable value, and distinct input roots need not be disjoint.
    pub(crate) fn with_scalar_input_domain(
        mut self,
        pointer: CPointerValue,
        c_type: CType,
    ) -> Result<Self, String> {
        if !Self::is_complete_scalar_designation(&pointer, c_type) {
            return Err("scalar input requires its complete scalar designation".into());
        }
        if let Some(held) = self.heap.scalar_input_domains.get(pointer.pointer()) {
            return if *held == c_type {
                Ok(self)
            } else {
                Err("conflicting scalar input types at the same address".into())
            };
        }
        if self
            .blocks
            .get(&pointer.pointer().block)
            .and_then(|block| block.declared_object.as_ref())
            .is_some()
            && !self.has_scalar_object_domain(&pointer, c_type)
        {
            return Err("scalar input conflicts with the declared object".into());
        }
        let diagnostic_base = self.clone();
        Arc::make_mut(&mut self.heap)
            .scalar_input_domains
            .insert(pointer.pointer().clone(), c_type);
        self.record_diagnostic_transform(
            "scalar input domain",
            vec![diagnostic_base],
            vec![CValue::Pointer(pointer)],
        );
        Ok(self)
    }

    fn is_complete_scalar_designation(pointer: &CPointerValue, c_type: CType) -> bool {
        let Some(PointerDesignation::Object {
            root,
            path,
            base,
            element_type,
            stride,
            count,
        }) = pointer.designation()
        else {
            return false;
        };
        *element_type == c_type
            && c_type.byte_width() > 0
            && c_type.pointer_to().is_some()
            && root == base
            && base == pointer.pointer()
            && path.is_empty()
            && *stride == c_type.byte_width()
            && *count == SharedIntegerTerm::from(IntegerTerm::constant_i64(1))
    }

    /// Authenticate the carried selection, rather than searching for a typed
    /// cell at the requested numeric address. In particular, a one-past member
    /// pointer cannot acquire a sibling's identity here.
    pub(crate) fn has_scalar_object_domain(&self, pointer: &CPointerValue, c_type: CType) -> bool {
        if let Some(PointerDesignation::InputSelected {
            base,
            element_type,
            stride,
            count,
            ..
        }) = pointer.designation()
        {
            return pointer.pointer() == base
                && *element_type == c_type
                && *stride == c_type.byte_width()
                && *count == SharedIntegerTerm::from(IntegerTerm::constant_i64(1))
                && self
                    .authenticated_input_selection(pointer, &PureFactContext::new())
                    .is_some_and(|guards| {
                        guards
                            .iter()
                            .all(|guard| guard == &ConditionTerm::Constant(true))
                    });
        }
        if !Self::is_complete_scalar_designation(pointer, c_type) {
            return self
                .checked_record_selection(pointer)
                .is_some_and(|(_, path, selected)| !path.is_empty() && selected == c_type);
        }
        if !Self::is_complete_scalar_designation(pointer, c_type)
            || self.is_ended_local_address(pointer.pointer())
            || self.is_deallocated_heap_address(pointer.pointer(), &PureFactContext::new())
            || pointer.is_null()
        {
            return false;
        }
        crate::instrumentation::record_deterministic_work(1);
        if let Some(declaration) = self
            .blocks
            .get(&pointer.pointer().block)
            .and_then(|block| block.declared_object.as_ref())
        {
            return pointer.pointer().offset.as_const() == Some(0)
                && matches!(declaration, CDeclaredObject::Scalar(held) if *held == c_type);
        }
        self.heap.scalar_input_domains.get(pointer.pointer()) == Some(&c_type)
    }

    /// Address formation for a declared scalar selects that declaration. This
    /// helper is not used by casts, memory lookup or ownership acquisition.
    pub(in crate::kernel) fn declared_scalar_pointer(
        &self,
        pointer: &Pointer,
        c_type: CType,
    ) -> Option<CPointerValue> {
        let value = CPointerValue::new(pointer.clone(), c_type.pointer_to()?).with_designation(
            PointerDesignation::Object {
                root: pointer.clone(),
                path: Arc::from([]),
                base: pointer.clone(),
                element_type: c_type,
                stride: c_type.byte_width(),
                count: IntegerTerm::constant_i64(1).into(),
            },
        );
        self.has_scalar_object_domain(&value, c_type)
            .then_some(value)
    }

    /// Authenticate an actual scalar array declaration. Its element count is
    /// never reconstructed from byte ownership or the allocation's extent.
    pub(in crate::kernel) fn has_declared_array_domain(&self, pointer: &CPointerValue) -> bool {
        let at_base = match pointer.designation() {
            Some(PointerDesignation::Object { base, .. })
            | Some(PointerDesignation::InputSelected { base, .. }) => pointer.pointer() == base,
            _ => false,
        };
        at_base
            && self
                .authenticated_array_domain(pointer, &PureFactContext::new())
                .is_some_and(|guards| {
                    guards
                        .iter()
                        .all(|guard| guard == &ConditionTerm::Constant(true))
                })
    }

    pub(in crate::kernel) fn declared_array_pointer(
        &self,
        address: &Pointer,
        element_type: CType,
        count: u32,
    ) -> Option<CPointerValue> {
        let value = CPointerValue::new(address.clone(), element_type.pointer_to()?)
            .with_designation(PointerDesignation::Object {
                root: address.clone(),
                path: Arc::from([]),
                base: address.clone(),
                element_type: element_type.scalar_array_type(count)?,
                stride: count.checked_mul(element_type.byte_width())?,
                count: IntegerTerm::constant_i64(1).into(),
            });
        let (value, guards) = self.guarded_declared_array_decay(&value, &PureFactContext::new())?;
        guards
            .iter()
            .all(|guard| guard == &ConditionTerm::Constant(true))
            .then_some(value)
    }

    /// Array decay selects the actual declared member array while keeping its
    /// enclosing root/path. It cannot flatten an array of records or recover a
    /// member merely from a raw numeric address.
    #[cfg(test)]
    pub(in crate::kernel) fn checked_member_array_pointer(
        &self,
        object: &CPointerValue,
    ) -> Option<CPointerValue> {
        let (pointer, guards) =
            self.guarded_declared_array_decay(object, &PureFactContext::new())?;
        guards
            .iter()
            .all(|guard| guard == &ConditionTerm::Constant(true))
            .then_some(pointer)
    }

    pub(in crate::kernel) fn guarded_member_array_pointer(
        &self,
        object: &CPointerValue,
        assumptions: &PureFactContext,
    ) -> Option<(CPointerValue, Vec<ConditionTerm>)> {
        self.guarded_declared_array_decay(object, assumptions)
    }

    /// Authenticate a retained descriptor at its selected base. The executable
    /// operation separately checks the current position against this domain;
    /// changing address spelling here does not issue a different descriptor.
    pub(in crate::kernel) fn authenticated_pointer_domain_at_base(
        &self,
        pointer: &CPointerValue,
    ) -> bool {
        if matches!(
            pointer.designation(),
            Some(PointerDesignation::InputSelected { .. })
        ) {
            return self
                .authenticated_input_selection(pointer, &PureFactContext::new())
                .is_some_and(|guards| {
                    guards
                        .iter()
                        .all(|guard| guard == &ConditionTerm::Constant(true))
                });
        }
        let Some(PointerDesignation::Object {
            base, element_type, ..
        }) = pointer.designation()
        else {
            return false;
        };
        let at_base = pointer.clone().with_pointer(base.clone());
        self.has_declared_array_domain(&at_base)
            || self.has_scalar_object_domain(&at_base, *element_type)
            || self.checked_record_selection(&at_base).is_some()
    }

    /// Authenticate a retained record-root/path descriptor against declarations
    /// or admitted native input requirements. Address coincidence is insufficient.
    fn checked_record_selection<'a>(
        &'a self,
        pointer: &CPointerValue,
    ) -> Option<(&'a CAggregateLayout, Vec<String>, CType)> {
        let PointerDesignation::Object {
            root,
            path,
            base,
            element_type,
            stride,
            count,
        } = pointer.designation()?
        else {
            return None;
        };
        if base != pointer.pointer()
            || *count != SharedIntegerTerm::from(IntegerTerm::constant_i64(1))
            || self.is_ended_local_address(root)
            || self.is_deallocated_heap_address(root, &PureFactContext::new())
            || pointer.is_null()
        {
            return None;
        }
        let layout = match self
            .blocks
            .get(&root.block)
            .and_then(|block| block.declared_object.as_ref())
        {
            Some(CDeclaredObject::Aggregate(layout)) if root.offset.as_const() == Some(0) => {
                layout.as_ref()
            }
            Some(_) => return None,
            None => self.heap.object_input_domains.get(root)?.as_ref(),
        };
        if layout.scalar_array().is_some() || !layout.unions().is_empty() {
            return None;
        }
        // Actual C/Rust declarations use structural layouts. Native C++
        // callers additionally match the authenticated nominal identity in
        // selects_layout_path; absent identity never substitutes for it.
        let path = path
            .iter()
            .map(|selection| match selection {
                PointerDomainSelection::Member(name) => Some(name.clone()),
                PointerDomainSelection::Element(_) => None,
            })
            .collect::<Option<Vec<_>>>()?;
        let (offset, selected) = if path.is_empty() {
            (0, CType::UInt8Array(layout.size_bytes()))
        } else {
            layout.member_at_path(&path)?
        };
        if *element_type != selected
            || *stride != selected.byte_width()
            || selected.byte_width() == 0
            || *base != root.offset_by_bytes(offset)
        {
            return None;
        }
        Some((layout, path, selected))
    }

    pub(crate) fn has_aggregate_object_domain(
        &self,
        pointer: &CPointerValue,
        expected: &CAggregateLayout,
    ) -> bool {
        if let Some(PointerDesignation::InputSelected {
            input,
            origin,
            path,
            base,
            element_type,
            stride,
            count,
        }) = pointer.designation()
        {
            return pointer.pointer() == base
                && *element_type == CType::UInt8Array(expected.size_bytes())
                && *stride == expected.size_bytes()
                && *count == SharedIntegerTerm::from(IntegerTerm::constant_i64(1))
                && self
                    .authenticated_input_selection(pointer, &PureFactContext::new())
                    .is_some_and(|guards| {
                        guards
                            .iter()
                            .all(|guard| guard == &ConditionTerm::Constant(true))
                    })
                && self.input_selection_parts(input, origin, path).is_some_and(
                    |(layout, _, _, members)| layout.selects_layout_path(&members, expected),
                );
        }
        if let Some((element, count)) = expected.scalar_array() {
            return self.has_declared_array_domain(pointer)
                && matches!(pointer.designation(), Some(PointerDesignation::Object { element_type, count: held_count, .. })
                    if *element_type == element && *held_count == SharedIntegerTerm::from(IntegerTerm::constant_i64(i64::from(count))))
                && match pointer.designation() {
                    Some(PointerDesignation::Object { root, path, .. }) if path.is_empty() => {
                        match self
                            .blocks
                            .get(&root.block)
                            .and_then(|block| block.declared_object.as_ref())
                        {
                            Some(CDeclaredObject::Aggregate(layout)) => {
                                layout.selects_layout_path(&[], expected)
                            }
                            Some(_) => false,
                            None => self
                                .heap
                                .object_input_domains
                                .get(root)
                                .is_some_and(|layout| layout.selects_layout_path(&[], expected)),
                        }
                    }
                    _ => false,
                };
        }
        self.checked_record_selection(pointer)
            .is_some_and(|(layout, path, selected)| {
                selected == CType::UInt8Array(expected.size_bytes())
                    && layout.selects_layout_path(&path, expected)
            })
    }

    /// Issue a root descriptor at an actual aggregate declaration/address
    /// producer, never when a cast or byte lookup happens to find its block.
    pub(in crate::kernel) fn declared_aggregate_pointer(
        &self,
        address: &Pointer,
        layout: &CAggregateLayout,
    ) -> Option<CPointerValue> {
        if !layout.unions().is_empty() {
            return None;
        }
        if let Some((element, count)) = layout.scalar_array() {
            let value = self.declared_array_pointer(address, element, count)?;
            return self
                .has_aggregate_object_domain(&value, layout)
                .then_some(value);
        }
        let value = Self::aggregate_input_pointer(address.clone(), layout, CType::UInt8Pointer);
        self.has_aggregate_object_domain(&value, layout)
            .then_some(value)
    }

    pub(in crate::kernel) fn aggregate_input_pointer(
        address: Pointer,
        layout: &CAggregateLayout,
        pointer_type: CType,
    ) -> CPointerValue {
        if let Some((element, count)) = layout.scalar_array() {
            return CPointerValue::new(address.clone(), pointer_type).with_designation(
                PointerDesignation::Object {
                    root: address.clone(),
                    path: Arc::from([]),
                    base: address,
                    element_type: element,
                    stride: element.byte_width(),
                    count: IntegerTerm::constant_i64(i64::from(count)).into(),
                },
            );
        }
        CPointerValue::new(address.clone(), pointer_type).with_designation(
            PointerDesignation::Object {
                root: address.clone(),
                path: Arc::from([]),
                base: address,
                element_type: CType::UInt8Array(layout.size_bytes()),
                stride: layout.size_bytes(),
                count: IntegerTerm::constant_i64(1).into(),
            },
        )
    }

    pub(in crate::kernel) fn checked_member_pointer(
        &self,
        object: &CPointerValue,
        selection: &CAggregateMemberSelection,
    ) -> Option<CPointerValue> {
        if matches!(
            object.designation(),
            Some(
                PointerDesignation::Unresolved(_)
                    | PointerDesignation::Loaded(_)
                    | PointerDesignation::InputSelected { .. }
            )
        ) {
            let (pointer, guards) =
                self.guarded_native_record_selection(object, selection, &PureFactContext::new())?;
            return guards
                .iter()
                .all(|guard| guard == &ConditionTerm::Constant(true))
                .then_some(pointer);
        }
        let resolved_object;
        let object = if matches!(
            object.designation(),
            Some(PointerDesignation::Unresolved(_) | PointerDesignation::Loaded(_))
        ) {
            resolved_object = self.checked_native_record_pointer(object)?;
            &resolved_object
        } else {
            object
        };

        if !self.has_aggregate_object_domain(object, &selection.layout) {
            return None;
        }
        let (offset, value_type) = selection.layout.member_at_path(&selection.path)?;
        if value_type != selection.value_type {
            return None;
        }
        let PointerDesignation::Object { root, path, .. } = object.designation()? else {
            return None;
        };
        let mut selected_path = path.to_vec();
        selected_path.extend(
            selection
                .path
                .iter()
                .cloned()
                .map(PointerDomainSelection::Member),
        );
        let address = object.pointer().offset_by_bytes(offset);
        Some(
            object
                .clone()
                .with_pointer(address.clone())
                .with_type(value_type.pointer_to().unwrap_or(CType::Int32Pointer))
                .with_designation(PointerDesignation::Object {
                    root: root.clone(),
                    path: selected_path.into(),
                    base: address,
                    element_type: value_type,
                    stride: value_type.byte_width(),
                    count: IntegerTerm::constant_i64(1).into(),
                }),
        )
    }

    /// Select a relative child of an authenticated record carrier. The root
    /// layout comes from its declaration/input witness, never an address
    /// search; the existing selected path remains part of the result domain.
    pub(in crate::kernel) fn checked_member_pointer_by_path(
        &self,
        object: &CPointerValue,
        relative_path: &[String],
    ) -> Option<CPointerValue> {
        if matches!(
            object.designation(),
            Some(
                PointerDesignation::Unresolved(_)
                    | PointerDesignation::Loaded(_)
                    | PointerDesignation::InputSelected { .. }
            )
        ) {
            let (pointer, guards) = self.guarded_member_pointer_by_path(
                object,
                relative_path,
                &PureFactContext::new(),
            )?;
            return guards
                .iter()
                .all(|guard| guard == &ConditionTerm::Constant(true))
                .then_some(pointer);
        }
        let resolved_object;
        let object = if matches!(
            object.designation(),
            Some(PointerDesignation::Unresolved(_) | PointerDesignation::Loaded(_))
        ) {
            resolved_object = self.checked_native_record_pointer(object)?;
            &resolved_object
        } else {
            object
        };

        let (_, mut selected_path, selected_type) = self.checked_record_selection(object)?;
        if !matches!(selected_type, CType::UInt8Array(_)) {
            return None;
        }
        if relative_path.is_empty() {
            return Some(object.clone());
        }
        let PointerDesignation::Object { root, .. } = object.designation()? else {
            return None;
        };
        let layout = match self
            .blocks
            .get(&root.block)
            .and_then(|block| block.declared_object.as_ref())
        {
            Some(CDeclaredObject::Aggregate(layout)) => layout.clone(),
            Some(_) => return None,
            None => self.heap.object_input_domains.get(root)?.clone(),
        };
        selected_path.extend_from_slice(relative_path);
        let (_, value_type) = layout.member_at_path(&selected_path)?;
        let selection = CAggregateMemberSelection {
            layout: layout.clone(),
            path: selected_path.into(),
            value_type,
        };
        let root_object = Self::aggregate_input_pointer(root.clone(), &layout, object.c_type())
            .with_pointee_volatile(object.pointee_volatile())
            .with_pointee_constant(object.pointee_constant());
        self.checked_member_pointer(&root_object, &selection)
    }

    pub(in crate::kernel) fn guarded_member_pointer_by_path(
        &self,
        object: &CPointerValue,
        relative_path: &[String],
        assumptions: &PureFactContext,
    ) -> Option<(CPointerValue, Vec<ConditionTerm>)> {
        if matches!(
            object.designation(),
            Some(PointerDesignation::Object { .. })
        ) {
            return self
                .checked_member_pointer_by_path(object, relative_path)
                .map(|pointer| (pointer, vec![]));
        }
        let mut guards = vec![];
        let (root_object, layout, mut members) = if let Some(PointerDesignation::InputSelected {
            input,
            origin,
            path,
            base,
            element_type,
            ..
        }) = object.designation()
        {
            if !matches!(element_type, CType::UInt8Array(_)) {
                return None;
            }
            guards.extend(self.authenticated_input_selection(object, assumptions)?);
            guards.push(ConditionTerm::pointer_equal(
                object.pointer().clone(),
                base.clone(),
            ));
            let (layout, _, _, members) = self.input_selection_parts(input, origin, path)?;
            let member_offset = if members.is_empty() {
                0
            } else {
                layout.member_at_path(&members)?.0
            };
            let row = self.heap.native_record_inputs.get(input)?;
            let record_start = Pointer {
                block: object.block.clone(),
                offset: match object
                    .offset
                    .as_const()
                    .and_then(|offset| offset.checked_sub(i64::from(member_offset)))
                {
                    Some(offset) => PointerOffsetTerm::Constant(offset),
                    None => PointerOffsetTerm::Add(
                        Box::new(object.offset.clone()),
                        Box::new(PointerOffsetTerm::Constant(-i64::from(member_offset))),
                    ),
                },
            };
            let root_object = row
                .origin
                .clone()
                .with_pointer(record_start)
                .with_pointee_constant(object.pointee_constant())
                .with_pointee_volatile(object.pointee_volatile());
            (root_object, self.input_record_layout(object)?, members)
        } else {
            let layout = self.input_record_layout(object)?;
            (object.clone(), layout, vec![])
        };
        members.extend_from_slice(relative_path);
        let value_type = if members.is_empty() {
            CType::UInt8Array(layout.size_bytes())
        } else {
            layout.member_at_path(&members)?.1
        };
        let selection = CAggregateMemberSelection {
            layout,
            path: members.into(),
            value_type,
        };
        let (pointer, selection_guards) =
            self.guarded_native_record_selection(&root_object, &selection, assumptions)?;
        guards.extend(selection_guards);
        Some((pointer, guards))
    }

    /// Admit a source-typed native input promise. Callers must check the exact
    /// typed resource occurrence or interface obligation before using this
    /// trusted entry operation. It grants no memory or initialization.
    pub(in crate::kernel) fn with_native_record_input(
        mut self,
        pointer: CPointerValue,
        layout: Arc<CAggregateLayout>,
    ) -> Result<Self, String> {
        if layout.size_bytes() == 0
            || layout.scalar_array().is_some()
            || !layout.unions().is_empty()
        {
            return Err("native record input requires a supported record layout".into());
        }
        if matches!(
            pointer.designation(),
            Some(PointerDesignation::Object { .. } | PointerDesignation::InputSelected { .. })
        ) {
            return if self.has_aggregate_object_domain(&pointer, &layout) {
                Ok(self)
            } else {
                Err("native record input conflicts with its retained designation".into())
            };
        }
        let identity = Self::native_record_input_identity(&pointer)
            .ok_or("native record input requires an exact input identity")?;
        if !pointer.c_type().is_object_pointer()
            || pointer.is_null()
            || self.is_ended_local_address(pointer.pointer())
            || self.is_deallocated_heap_address(pointer.pointer(), &PureFactContext::new())
        {
            return Err("native record input requires a live nonnull object address".into());
        }
        let record =
            Self::aggregate_input_pointer(pointer.pointer().clone(), &layout, pointer.c_type());
        if self
            .blocks
            .get(&pointer.block)
            .is_some_and(|block| block.declared_object.is_some())
            && !self.has_aggregate_object_domain(&record, &layout)
        {
            return Err("native record input conflicts with the declared object".into());
        }
        let row = CNativeRecordInput {
            origin: pointer,
            kind: CNativeInputKind::Record {
                layout: layout.clone(),
            },
        };
        if let Some(held) = self.heap.native_record_inputs.get(&identity) {
            return if held == &row && self.checked_native_record_pointer(&row.origin).is_some() {
                Ok(self)
            } else {
                Err("conflicting native record input identity".into())
            };
        }
        if self
            .heap
            .object_input_domains
            .get(row.origin.pointer())
            .is_some_and(|held| held != &layout)
        {
            return Err("native record input conflicts with the retained object layout".into());
        }
        let diagnostic_base = self.clone();
        let base = intern_derivation_base(&mut self);
        let origin = row.origin.clone();
        let heap = Arc::make_mut(&mut self.heap);
        heap.object_input_domains
            .insert(origin.pointer().clone(), layout.clone());
        let mut identities = heap
            .native_record_input_origins
            .get(origin.pointer())
            .cloned()
            .unwrap_or_default();
        identities.insert(identity.clone());
        heap.native_record_input_origins
            .insert(origin.pointer().clone(), identities);
        heap.native_record_inputs.insert(identity.clone(), row);
        // A typed validity premise changes no stored bytes. Keep the exact
        // existing no-write memory edge for pointer/scalar read identities.
        record_c_memory_derivation(&mut self, CMemoryDerivation::CellsForgotten { base });
        self.record_diagnostic_transform(
            "native record input",
            vec![diagnostic_base],
            vec![CValue::Pointer(origin)],
        );
        Ok(self)
    }

    /// Admit only a source-typed guaranteed prefix, never a complete array
    /// descriptor or an ownership/initialization fact.
    #[cfg(test)]
    pub(in crate::kernel) fn with_native_input_span(
        self,
        pointer: CPointerValue,
        element_type: CType,
        count: SharedIntegerTerm,
    ) -> Result<Self, String> {
        self.with_typed_input_span(
            pointer,
            element_type,
            count,
            CTypedAccessPolicy::NativeObjectOnly,
        )
    }

    /// Source admission only: the valid slice signature promises bounded
    /// backing geometry, including a valid nonnull carrier for an empty slice.
    pub(in crate::kernel) fn with_native_slice_input(
        self,
        pointer: CPointerValue,
        element_type: CType,
        count: SharedIntegerTerm,
    ) -> Result<Self, String> {
        self.admit_typed_input_span(
            pointer,
            element_type,
            count,
            CTypedAccessPolicy::NativeObjectOnly,
            true,
        )
    }

    pub(in crate::kernel) fn with_typed_input_span(
        self,
        pointer: CPointerValue,
        element_type: CType,
        count: SharedIntegerTerm,
        policy: CTypedAccessPolicy,
    ) -> Result<Self, String> {
        self.admit_typed_input_span(pointer, element_type, count, policy, false)
    }

    fn admit_typed_input_span(
        mut self,
        pointer: CPointerValue,
        element_type: CType,
        count: SharedIntegerTerm,
        policy: CTypedAccessPolicy,
        source_slice: bool,
    ) -> Result<Self, String> {
        let width = element_type.byte_width();
        if width == 0
            || element_type.array_element_type().is_some()
            || element_type.pointer_to().is_none()
            || (source_slice && pointer.c_type().pointee_type() != Some(element_type))
        {
            return Err("native input span requires a supported scalar element type".into());
        }
        if count.as_const().is_some_and(|count| {
            count < &num_bigint::BigInt::from(0)
                || count
                    > &num_bigint::BigInt::from(
                        crate::kernel::eval::pointer_domains::native_prefix_element_limit(width),
                    )
        }) {
            return Err("native input span requires a nonnegative bounded byte extent".into());
        }
        let identity = Self::native_record_input_identity(&pointer)
            .ok_or("native input span requires an exact unresolved or loaded identity")?;
        if !pointer.c_type().is_object_pointer()
            || pointer.is_null()
            || self.is_ended_local_address(pointer.pointer())
            || self.is_deallocated_heap_address(pointer.pointer(), &PureFactContext::new())
        {
            return Err("native input span requires a live nonnull address".into());
        }
        // A known declaration is definitive. Trusted unknown-input admission
        // cannot reinterpret a known object or change its declared extent.
        if self
            .blocks
            .get(&pointer.block)
            .is_some_and(|block| block.declared_object.is_some())
        {
            return Err("native input span cannot replace a known declaration".into());
        }
        let row = CNativeRecordInput {
            origin: pointer,
            kind: if source_slice {
                CNativeInputKind::TypedSlice {
                    element_type,
                    count,
                }
            } else {
                CNativeInputKind::TypedPrefix {
                    element_type,
                    count,
                    policy,
                }
            },
        };
        if let Some(held) = self.heap.native_record_inputs.get(&identity) {
            if held == &row {
                return Ok(self);
            }
            let (
                CNativeInputKind::TypedPrefix {
                    element_type: held_type,
                    count: held_count,
                    policy: held_policy,
                },
                CNativeInputKind::TypedPrefix {
                    element_type: new_type,
                    count: new_count,
                    policy: new_policy,
                },
            ) = (&held.kind, &row.kind)
            else {
                return Err("conflicting native input witness".into());
            };
            if held.origin != row.origin || held_type != new_type || held_policy != new_policy {
                return Err("conflicting native input witness".into());
            }
            let (Some(held_count), Some(new_count)) = (held_count.as_const(), new_count.as_const())
            else {
                return Err("native input prefix extents have no proven ordering".into());
            };
            if held_count >= new_count {
                return Ok(self);
            }
            // Both promises name this exact carrier/type/policy. Retain the
            // larger literal guarantee; this issues no bytes or initialized cells.
        }
        let diagnostic_base = self.clone();
        let base = intern_derivation_base(&mut self);
        let origin = row.origin.clone();
        let heap = Arc::make_mut(&mut self.heap);
        let mut identities = heap
            .native_record_input_origins
            .get(origin.pointer())
            .cloned()
            .unwrap_or_default();
        identities.insert(identity.clone());
        heap.native_record_input_origins
            .insert(origin.pointer().clone(), identities);
        heap.native_record_inputs.insert(identity, row);
        record_c_memory_derivation(&mut self, CMemoryDerivation::CellsForgotten { base });
        self.record_diagnostic_transform(
            "native typed prefix",
            vec![diagnostic_base],
            vec![CValue::Pointer(origin)],
        );
        Ok(self)
    }

    pub(in crate::kernel) fn native_input_span_policy(
        &self,
        pointer: &CPointerValue,
    ) -> Option<CTypedAccessPolicy> {
        match &self.native_input_witness(pointer)?.kind {
            CNativeInputKind::TypedPrefix { policy, .. } => Some(*policy),
            CNativeInputKind::TypedSlice { .. } => Some(CTypedAccessPolicy::NativeObjectOnly),
            _ => None,
        }
    }

    /// Allocation-backed scalar access is a producer property, not a live-map
    /// claim or an object declaration. Pending and retired rows do not qualify.
    /// The allocator's success transition uses its original pending identity
    /// to retain the exact produced carrier in the allocation token.
    pub(in crate::kernel) fn resolved_allocated_scalar_pointer(
        &self,
        pending_base: &Pointer,
    ) -> Option<CPointerValue> {
        let PointerBlock::Symbolic(identity) = pending_base.block else {
            return None;
        };
        if pending_base != &Pointer::symbolic(identity) {
            return None;
        }
        let row = self
            .heap
            .native_record_inputs
            .get(&CNativeInputIdentity::Unresolved(identity))?;
        if row.origin.pointer()
            != &(Pointer {
                block: PointerBlock::Heap(identity.0),
                offset: PointerOffsetTerm::Constant(0),
            })
        {
            return None;
        }
        self.allocated_scalar_extent(&row.origin)
            .map(|(origin, _, _)| origin)
    }

    pub(in crate::kernel) fn allocated_scalar_extent(
        &self,
        pointer: &CPointerValue,
    ) -> Option<(CPointerValue, CType, SharedIntegerTerm)> {
        let row = self.native_input_witness(pointer)?;
        let CNativeInputKind::AllocatedScalar {
            element_type,
            bytes,
        } = &row.kind
        else {
            return None;
        };
        if !matches!(row.origin.block, PointerBlock::Heap(_))
            || row.origin.offset != PointerOffsetTerm::Constant(0)
        {
            return None;
        }
        let live_bytes = self.live_heap_block_size(row.origin.pointer())?;
        let observed = Self::allocated_byte_extent(live_bytes)?;
        if &observed != bytes {
            return None;
        }
        Some((row.origin.clone(), *element_type, bytes.clone()))
    }

    fn allocated_byte_extent(bytes: &Bitvector32Term) -> Option<SharedIntegerTerm> {
        crate::kernel::eval::pointer_domains::native_count_observation(
            MachineIntegerType::UInt32,
            crate::kernel::spec::c_value_bitvector_term(&CValue::UInt32(bytes.clone()))?,
        )
        .map(Into::into)
    }

    pub(in crate::kernel) fn native_input_span(
        &self,
        pointer: &CPointerValue,
    ) -> Option<(CPointerValue, CType, SharedIntegerTerm)> {
        let row = self.native_input_witness(pointer)?;
        let (CNativeInputKind::TypedPrefix {
            element_type,
            count,
            ..
        }
        | CNativeInputKind::TypedSlice {
            element_type,
            count,
        }) = &row.kind
        else {
            return None;
        };
        Some((row.origin.clone(), *element_type, count.clone()))
    }

    pub(in crate::kernel) fn native_input_is_slice(&self, pointer: &CPointerValue) -> bool {
        self.native_input_witness(pointer)
            .is_some_and(|row| matches!(row.kind, CNativeInputKind::TypedSlice { .. }))
    }

    pub(in crate::kernel) fn with_native_record_prefix(
        mut self,
        pointer: CPointerValue,
        layout: Arc<CAggregateLayout>,
        count: SharedIntegerTerm,
    ) -> Result<Self, String> {
        if layout.size_bytes() == 0
            || layout.scalar_array().is_some()
            || !layout.unions().is_empty()
            || count.as_const().is_some_and(|count| {
                count < &num_bigint::BigInt::from(0)
                    || count
                        > &num_bigint::BigInt::from(
                            crate::kernel::eval::pointer_domains::native_prefix_element_limit(
                                layout.size_bytes(),
                            ),
                        )
            })
        {
            return Err("native record prefix requires a supported bounded record extent".into());
        }
        let identity = Self::native_record_input_identity(&pointer)
            .ok_or("native record prefix requires an exact input identity")?;
        if pointer.is_null()
            || self.is_ended_local_address(pointer.pointer())
            || self.is_deallocated_heap_address(pointer.pointer(), &PureFactContext::new())
            || self
                .blocks
                .get(&pointer.block)
                .is_some_and(|block| block.declared_object.is_some())
        {
            return Err("native record prefix cannot replace a dead or declared object".into());
        }
        let row = CNativeRecordInput {
            origin: pointer,
            kind: CNativeInputKind::RecordPrefix { layout, count },
        };
        if let Some(held) = self.heap.native_record_inputs.get(&identity) {
            return if held == &row {
                Ok(self)
            } else {
                Err("conflicting native input witness".into())
            };
        }
        let diagnostic_base = self.clone();
        let base = intern_derivation_base(&mut self);
        let origin = row.origin.clone();
        let heap = Arc::make_mut(&mut self.heap);
        let mut identities = heap
            .native_record_input_origins
            .get(origin.pointer())
            .cloned()
            .unwrap_or_default();
        identities.insert(identity.clone());
        heap.native_record_input_origins
            .insert(origin.pointer().clone(), identities);
        heap.native_record_inputs.insert(identity, row);
        record_c_memory_derivation(&mut self, CMemoryDerivation::CellsForgotten { base });
        self.record_diagnostic_transform(
            "native record prefix",
            vec![diagnostic_base],
            vec![CValue::Pointer(origin)],
        );
        Ok(self)
    }

    pub(in crate::kernel) fn native_record_prefix(
        &self,
        pointer: &CPointerValue,
    ) -> Option<(CPointerValue, Arc<CAggregateLayout>, SharedIntegerTerm)> {
        let row = self.native_input_witness(pointer)?;
        let CNativeInputKind::RecordPrefix { layout, count } = &row.kind else {
            return None;
        };
        Some((row.origin.clone(), layout.clone(), count.clone()))
    }

    pub(super) fn input_selection_parts<'a>(
        &'a self,
        input: &CNativeInputIdentity,
        origin: &Pointer,
        path: &[PointerDomainSelection],
    ) -> Option<(
        &'a CAggregateLayout,
        SharedIntegerTerm,
        SharedIntegerTerm,
        Vec<String>,
    )> {
        crate::instrumentation::record_deterministic_work(1);
        let row = self.heap.native_record_inputs.get(input)?;
        if row.origin.pointer() != origin || self.native_input_witness(&row.origin).is_none() {
            return None;
        }
        let (layout, count, index, members) = match &row.kind {
            CNativeInputKind::Record { layout } => (
                layout.as_ref(),
                IntegerTerm::constant_i64(1).into(),
                IntegerTerm::constant_i64(0).into(),
                path,
            ),
            CNativeInputKind::RecordPrefix { layout, count } => {
                let (PointerDomainSelection::Element(index), members) = path.split_first()? else {
                    return None;
                };
                (layout.as_ref(), count.clone(), index.clone(), members)
            }
            _ => return None,
        };
        if layout.size_bytes() == 0 || !layout.unions().is_empty() {
            return None;
        }
        let members = members
            .iter()
            .take_while(|part| matches!(part, PointerDomainSelection::Member(_)))
            .map(|part| match part {
                PointerDomainSelection::Member(name) => Some(name.clone()),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?;
        Some((layout, count, index, members))
    }

    /// Structural authentication returns the exact selected bounds as guards.
    /// The caller must discharge them before using this selected domain.
    pub(in crate::kernel) fn authenticated_input_selection(
        &self,
        pointer: &CPointerValue,
        assumptions: &PureFactContext,
    ) -> Option<Vec<ConditionTerm>> {
        let PointerDesignation::InputSelected {
            input,
            origin,
            path,
            base,
            element_type,
            stride,
            count,
        } = pointer.designation()?
        else {
            return None;
        };
        if let Some(guards) = self.authenticated_array_domain(pointer, assumptions) {
            return Some(guards);
        }
        let (layout, prefix, index, members) = self.input_selection_parts(input, origin, path)?;
        let (offset, selected) = if members.is_empty() {
            (0, CType::UInt8Array(layout.size_bytes()))
        } else {
            layout.member_at_path(&members)?
        };
        let row = self.heap.native_record_inputs.get(input)?;
        let member_path = if matches!(row.kind, CNativeInputKind::RecordPrefix { .. }) {
            &path[1..]
        } else {
            path.as_ref()
        };
        if member_path
            .iter()
            .any(|part| matches!(part, PointerDomainSelection::Element(_)))
        {
            return None;
        }
        let complete = *element_type == selected
            && *stride == selected.byte_width()
            && *count == SharedIntegerTerm::from(IntegerTerm::constant_i64(1));
        // All array decay (including one-dimensional arrays) is checked by
        // authenticated_array_domain above. A failed shape match must not
        // fall back to the old flat scalar extent.
        if !complete {
            return None;
        }
        let record_start = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::Add(
                Box::new(base.offset.clone()),
                Box::new(PointerOffsetTerm::Constant(-i64::from(offset))),
            ),
        };
        let actual_index = crate::kernel::eval::pointer_domains::domain_displacement(
            &record_start,
            origin,
            layout.size_bytes(),
            assumptions,
        )?;
        Some(vec![
            crate::kernel::eval::pointer_domains::domain_less_equal(
                IntegerTerm::constant_i64(0),
                prefix.as_ref().clone(),
            ),
            crate::kernel::eval::pointer_domains::domain_less_equal(
                prefix.as_ref().clone(),
                IntegerTerm::constant_i64(
                    crate::kernel::eval::pointer_domains::native_prefix_element_limit(
                        layout.size_bytes(),
                    ),
                ),
            ),
            crate::kernel::eval::pointer_domains::domain_less_equal(
                IntegerTerm::constant_i64(0),
                index.as_ref().clone(),
            ),
            crate::kernel::eval::pointer_domains::domain_less_than(
                index.as_ref().clone(),
                prefix.as_ref().clone(),
            ),
            crate::kernel::eval::pointer_domains::domain_equal(
                actual_index,
                index.as_ref().clone(),
            ),
        ])
    }

    pub(in crate::kernel) fn guarded_native_record_selection(
        &self,
        pointer: &CPointerValue,
        selection: &CAggregateMemberSelection,
        assumptions: &PureFactContext,
    ) -> Option<(CPointerValue, Vec<ConditionTerm>)> {
        if matches!(
            pointer.designation(),
            Some(PointerDesignation::Object { .. })
        ) {
            if selection.path.is_empty()
                && selection.value_type == CType::UInt8Array(selection.layout.size_bytes())
                && self.has_aggregate_object_domain(pointer, &selection.layout)
            {
                return Some((pointer.clone(), vec![]));
            }
            return self
                .checked_member_pointer(pointer, selection)
                .map(|pointer| (pointer, vec![]));
        }
        let mut guards = Vec::new();
        let (input, origin, mut path, layout, members) =
            if let Some(PointerDesignation::InputSelected {
                input,
                origin,
                path,
                base,
                ..
            }) = pointer.designation()
            {
                guards.extend(self.authenticated_input_selection(pointer, assumptions)?);
                guards.push(ConditionTerm::pointer_equal(
                    pointer.pointer().clone(),
                    base.clone(),
                ));
                let (layout, _, _, members) = self.input_selection_parts(input, origin, path)?;
                (
                    input.clone(),
                    origin.clone(),
                    path.to_vec(),
                    layout,
                    members,
                )
            } else {
                let row = self.native_input_witness(pointer)?;
                let input = Self::native_record_input_identity(&row.origin)?;
                let (layout, path) = match &row.kind {
                    CNativeInputKind::Record { layout } => {
                        guards.push(ConditionTerm::pointer_equal(
                            pointer.pointer().clone(),
                            row.origin.pointer().clone(),
                        ));
                        (layout.as_ref(), vec![])
                    }
                    CNativeInputKind::RecordPrefix { layout, .. } => {
                        let index = crate::kernel::eval::pointer_domains::domain_displacement(
                            pointer.pointer(),
                            row.origin.pointer(),
                            layout.size_bytes(),
                            assumptions,
                        )?;
                        (
                            layout.as_ref(),
                            vec![PointerDomainSelection::Element(index.into())],
                        )
                    }
                    _ => return None,
                };
                (input, row.origin.pointer().clone(), path, layout, vec![])
            };
        if !layout.selects_layout_path(&members, &selection.layout) {
            return None;
        }
        let (offset, value_type) = if selection.path.is_empty() {
            (0, CType::UInt8Array(selection.layout.size_bytes()))
        } else {
            selection.layout.member_at_path(&selection.path)?
        };
        if value_type != selection.value_type {
            return None;
        }
        path.extend(
            selection
                .path
                .iter()
                .cloned()
                .map(PointerDomainSelection::Member),
        );
        let address = Pointer {
            block: pointer.block.clone(),
            offset: match pointer
                .offset
                .as_const()
                .and_then(|base_offset| base_offset.checked_add(i64::from(offset)))
            {
                Some(offset) => PointerOffsetTerm::Constant(offset),
                None => PointerOffsetTerm::Add(
                    Box::new(pointer.offset.clone()),
                    Box::new(PointerOffsetTerm::Constant(i64::from(offset))),
                ),
            },
        };
        let selected = pointer
            .clone()
            .with_pointer(address.clone())
            .with_type(value_type.pointer_to().unwrap_or(CType::Int32Pointer))
            .with_designation(PointerDesignation::InputSelected {
                input,
                origin,
                path: path.into(),
                base: address,
                element_type: value_type,
                stride: value_type.byte_width(),
                count: IntegerTerm::constant_i64(1).into(),
            });
        guards.extend(self.authenticated_input_selection(&selected, assumptions)?);
        Some((selected, guards))
    }

    fn native_input_witness(&self, pointer: &CPointerValue) -> Option<&CNativeRecordInput> {
        let identity = match pointer.designation()? {
            PointerDesignation::Unresolved(identity) => CNativeInputIdentity::Unresolved(*identity),
            PointerDesignation::Loaded(identity) => CNativeInputIdentity::Loaded(identity.clone()),
            _ => return None,
        };
        crate::instrumentation::record_deterministic_work(1);
        let row = self.heap.native_record_inputs.get(&identity)?;
        if self.is_ended_local_address(row.origin.pointer())
            || self
                .heap
                .deallocated_allocations
                .contains_key(row.origin.pointer())
        {
            return None;
        }
        if self
            .blocks
            .get(&row.origin.block)
            .is_some_and(|block| block.declared_object.is_some())
        {
            let CNativeInputKind::Record { layout } = &row.kind else {
                return None;
            };
            let record = Self::aggregate_input_pointer(
                row.origin.pointer().clone(),
                layout,
                row.origin.c_type(),
            );
            if !self.has_aggregate_object_domain(&record, layout) {
                return None;
            }
        }
        if let CNativeInputIdentity::Loaded(origin) = &identity {
            crate::kernel::memory_provenance::paired_pointer_load_displacement(
                &pointer.clone().with_type(row.origin.c_type()),
                origin,
            )?;
        }
        Some(row)
    }

    /// Resolve only an exact typed-input identity, keeping the selected base
    /// separate from its current address displacement. Loaded inputs must
    /// carry the exact immutable full-pointer read named by their witness.
    pub(in crate::kernel) fn checked_native_record_pointer(
        &self,
        pointer: &CPointerValue,
    ) -> Option<CPointerValue> {
        if matches!(
            pointer.designation(),
            Some(PointerDesignation::InputSelected { .. })
        ) {
            return self
                .authenticated_input_selection(pointer, &PureFactContext::new())?
                .iter()
                .all(|guard| guard == &ConditionTerm::Constant(true))
                .then(|| pointer.clone());
        }
        if let Some(PointerDesignation::Object { base, .. }) = pointer.designation() {
            let at_base = pointer.clone().with_pointer(base.clone());
            return self
                .checked_record_selection(&at_base)
                .map(|_| pointer.clone());
        }
        let row = self.native_input_witness(pointer)?;
        let CNativeInputKind::Record { layout } = &row.kind else {
            return None;
        };
        let record = pointer
            .clone()
            .with_designation(PointerDesignation::InputSelected {
                input: Self::native_record_input_identity(&row.origin)?,
                origin: row.origin.pointer().clone(),
                path: Arc::from([]),
                base: row.origin.pointer().clone(),
                element_type: CType::UInt8Array(layout.size_bytes()),
                stride: layout.size_bytes(),
                count: IntegerTerm::constant_i64(1).into(),
            });
        self.authenticated_input_selection(&record, &PureFactContext::new())?
            .iter()
            .all(|guard| guard == &ConditionTerm::Constant(true))
            .then_some(record)
    }

    pub(in crate::kernel) fn input_record_layout(
        &self,
        pointer: &CPointerValue,
    ) -> Option<Arc<CAggregateLayout>> {
        let row = match pointer.designation()? {
            PointerDesignation::InputSelected { input, origin, .. } => {
                let row = self.heap.native_record_inputs.get(input)?;
                if row.origin.pointer() != origin {
                    return None;
                }
                self.native_input_witness(&row.origin)?
            }
            _ => self.native_input_witness(pointer)?,
        };
        match &row.kind {
            CNativeInputKind::Record { layout } | CNativeInputKind::RecordPrefix { layout, .. } => {
                Some(layout.clone())
            }
            _ => None,
        }
    }

    fn native_record_input_identity(pointer: &CPointerValue) -> Option<CNativeInputIdentity> {
        match pointer.designation()? {
            PointerDesignation::Unresolved(identity) => {
                Some(CNativeInputIdentity::Unresolved(*identity))
            }
            PointerDesignation::Loaded(identity) => {
                crate::kernel::memory_provenance::paired_pointer_load_displacement(
                    pointer, identity,
                )?;
                Some(CNativeInputIdentity::Loaded(identity.clone()))
            }
            _ => None,
        }
    }

    pub(in crate::kernel) fn map_native_record_inputs(
        &self,
        mut rewrite: impl FnMut(&CPointerValue) -> CPointerValue,
        mut rewrite_count: impl FnMut(&SharedIntegerTerm) -> SharedIntegerTerm,
    ) -> (
        SnapshotMap<CNativeInputIdentity, CNativeRecordInput>,
        SnapshotMap<Pointer, SnapshotSet<CNativeInputIdentity>>,
    ) {
        let mut mapped = SnapshotMap::default();
        let mut conflicts = BTreeSet::new();
        for row in self.heap.native_record_inputs.values() {
            crate::instrumentation::record_deterministic_work(1);
            let origin = rewrite(&row.origin);
            let Some(identity) = Self::native_record_input_identity(&origin) else {
                continue;
            };
            let row = CNativeRecordInput {
                origin,
                kind: match &row.kind {
                    CNativeInputKind::Record { layout } => CNativeInputKind::Record {
                        layout: layout.clone(),
                    },
                    CNativeInputKind::RecordPrefix { layout, count } => {
                        CNativeInputKind::RecordPrefix {
                            layout: layout.clone(),
                            count: rewrite_count(count),
                        }
                    }
                    CNativeInputKind::AllocatedScalar {
                        element_type,
                        bytes,
                    } => CNativeInputKind::AllocatedScalar {
                        element_type: *element_type,
                        bytes: rewrite_count(bytes),
                    },
                    CNativeInputKind::TypedSlice {
                        element_type,
                        count,
                    } => CNativeInputKind::TypedSlice {
                        element_type: *element_type,
                        count: rewrite_count(count),
                    },
                    CNativeInputKind::TypedPrefix {
                        element_type,
                        count,
                        policy,
                    } => CNativeInputKind::TypedPrefix {
                        element_type: *element_type,
                        count: rewrite_count(count),
                        policy: *policy,
                    },
                },
            };
            if conflicts.contains(&identity) {
                continue;
            }
            if mapped.get(&identity).is_some_and(|held| held != &row) {
                mapped.remove(&identity);
                conflicts.insert(identity);
            } else {
                mapped.insert(identity, row);
            }
        }
        let mut origins = SnapshotMap::<Pointer, SnapshotSet<CNativeInputIdentity>>::default();
        for (identity, row) in mapped.iter() {
            let mut identities = origins
                .get(row.origin.pointer())
                .cloned()
                .unwrap_or_default();
            identities.insert(identity.clone());
            origins.insert(row.origin.pointer().clone(), identities);
        }
        (mapped, origins)
    }

    pub(in crate::kernel) fn map_scalar_input_domains(
        &self,
        mut rewrite: impl FnMut(&Pointer) -> Pointer,
    ) -> SnapshotMap<Pointer, CType> {
        let mut mapped = SnapshotMap::<Pointer, CType>::default();
        let mut conflicts = BTreeSet::new();
        for (pointer, c_type) in self.heap.scalar_input_domains.iter() {
            let pointer = rewrite(pointer);
            if conflicts.contains(&pointer) {
                continue;
            }
            if mapped.get(&pointer).is_some_and(|held| held != c_type) {
                mapped.remove(&pointer);
                conflicts.insert(pointer);
            } else {
                mapped.insert(pointer, *c_type);
            }
        }
        mapped
    }

    /// Adds only a source contract's interface-entry object requirement.
    /// Actual calls discharge it against declarations or a retained requirement;
    /// raw markers and selecting a return destination never issue this fact.
    pub(crate) fn with_object_input_domain(
        mut self,
        pointer: Pointer,
        layout: &CAggregateLayout,
    ) -> Result<Self, String> {
        if let Some(held) = self.heap.object_input_domains.get(&pointer) {
            return if held.as_ref() == layout {
                Ok(self)
            } else {
                Err("conflicting object input layouts at the same address".into())
            };
        }
        let diagnostic_base = self.clone();
        Arc::make_mut(&mut self.heap)
            .object_input_domains
            .insert(pointer.clone(), Arc::new(layout.clone()));
        self.record_diagnostic_transform(
            "object input domain",
            vec![diagnostic_base],
            vec![CValue::pointer(pointer)],
        );
        Ok(self)
    }

    /// Discharges an interface's structural destination requirement. A known
    /// declaration is decisive: an input-domain assumption cannot override it.
    /// Otherwise only retained source-entry requirements in this exact block
    /// are candidates; possibly-aliasing unrelated input identities give no
    /// designation evidence.
    pub(in crate::kernel) fn has_object_layout_at(
        &self,
        pointer: &Pointer,
        layout: &CAggregateLayout,
        allow_records: bool,
    ) -> bool {
        let Some(offset) = pointer
            .offset
            .as_const()
            .and_then(|offset| u32::try_from(offset).ok())
        else {
            return false;
        };
        let matches = |held: &CAggregateLayout, relative| {
            if allow_records {
                held.selects_layout_at(relative, layout)
            } else {
                relative == 0 && held == layout
            }
        };
        if let Some(declaration) = self
            .blocks
            .get(&pointer.block)
            .and_then(|block| block.declared_object.as_ref())
        {
            return match declaration {
                CDeclaredObject::Scalar(_) | CDeclaredObject::Array { .. } => false,
                CDeclaredObject::Aggregate(held) => matches(held, offset),
            };
        }
        AliasCandidates::only_block(&pointer.block).any_entry(
            &self.heap.object_input_domains,
            |base, held| {
                crate::instrumentation::record_deterministic_work(1);
                base.offset
                    .as_const()
                    .and_then(|offset| u32::try_from(offset).ok())
                    .and_then(|base| offset.checked_sub(base))
                    .is_some_and(|relative| matches(held, relative))
            },
        )
    }

    /// A substitution can identify previously distinct inputs. Incompatible
    /// collided requirements supply no selection witness; never choose the
    /// last layout merely because it came last in a map traversal.
    pub(in crate::kernel) fn map_object_input_domains(
        &self,
        mut rewrite: impl FnMut(&Pointer) -> Pointer,
    ) -> SnapshotMap<Pointer, Arc<CAggregateLayout>> {
        let mut mapped = SnapshotMap::<Pointer, Arc<CAggregateLayout>>::default();
        let mut conflicts = BTreeSet::new();
        for (pointer, layout) in self.heap.object_input_domains.iter() {
            let pointer = rewrite(pointer);
            if conflicts.contains(&pointer) {
                continue;
            }
            if mapped.get(&pointer).is_some_and(|held| held != layout) {
                mapped.remove(&pointer);
                conflicts.insert(pointer);
            } else {
                mapped.insert(pointer, layout.clone());
            }
        }
        mapped
    }

    /// A conservative overlap query over only potentially aliasing tracked
    /// objects. Different symbolic spellings do not establish separation.
    #[cfg(test)]
    pub(in crate::kernel) fn may_read_uninitialized_object(
        &self,
        pointer: &Pointer,
        bytes: u32,
    ) -> bool {
        self.may_read_uninitialized_object_under(pointer, bytes, &PureFactContext::new())
    }

    /// Exclude only raw footprints whose separation from this read is checked
    /// in its fact context. Initialization and ownership remain independent.
    pub(in crate::kernel) fn may_read_uninitialized_object_under(
        &self,
        pointer: &Pointer,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        if bytes == 0 {
            return false;
        }
        AliasCandidates::of_block(&pointer.block).any_entry(
            &self.heap.uninitialized_objects,
            |base, size| {
                crate::instrumentation::record_deterministic_work(1);
                if *size == 0 {
                    return false;
                }
                if base.block == pointer.block
                    && let (Some(start), Some(at)) =
                        (base.offset.as_const(), pointer.offset.as_const())
                    && let (Some(end), Some(read_end)) = (
                        start.checked_add(i64::from(*size)),
                        at.checked_add(i64::from(bytes)),
                    )
                {
                    return at < end && start < read_end;
                }
                !assumptions.proves_stated_byte_separation(pointer, bytes, base, *size)
                    && !self.scalar_input_excludes_object_padding(
                        pointer,
                        bytes,
                        base,
                        *size,
                        assumptions,
                    )
            },
        )
    }

    /// In the admitted non-overlapping C++ object hierarchy, a scalar object
    /// inside a constructing record must be one of its declared value fields.
    /// Thus a checked scalar input separated from every field is outside the
    /// whole record. This is not a rule about arbitrary byte ownership: both
    /// object witnesses are required, and the record's padding stays raw.
    fn scalar_input_excludes_object_padding(
        &self,
        pointer: &Pointer,
        bytes: u32,
        base: &Pointer,
        size: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        let Some(scalar_type) = self.heap.scalar_input_domains.get(pointer) else {
            return false;
        };
        if scalar_type.byte_width() != bytes {
            return false;
        }
        let Some(layout) = self.heap.object_input_domains.get(base) else {
            return false;
        };
        if layout.declaration_identity().is_none()
            || layout.size_bytes() != size
            || !layout.unions().is_empty()
            || layout.fields().is_empty()
        {
            return false;
        }
        let mut previous_end = 0;
        layout.fields().iter().all(|field| {
            crate::instrumentation::record_deterministic_work(1);
            let width = field.c_type().byte_width();
            let Some(end) = field.offset_bytes().checked_add(width) else {
                return false;
            };
            if width == 0 || field.offset_bytes() < previous_end || end > size {
                return false;
            }
            previous_end = end;
            crate::kernel::memory_provenance::write_access_is_disjoint_from_load(
                &base.offset_by_bytes(field.offset_bytes()),
                width,
                pointer,
                bytes,
                assumptions,
            )
        })
    }

    pub(in crate::kernel) fn with_block_or_read_only(
        self,
        block: impl Into<PointerBlock>,
        size: u32,
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
        block: impl Into<PointerBlock>,
        size: u32,
    ) -> Self {
        let block = block.into();
        let base = intern_derivation_base(&mut self);
        std::sync::Arc::make_mut(&mut self.blocks).insert(block.clone(), CBlock::read_only(size));
        record_c_memory_derivation(&mut self, CMemoryDerivation::BlockDeclared { base, block });
        self
    }

    /// Adds a synthetic block without claiming that it was declared by a
    /// program transition. Symbolic aggregate return values use this to make
    /// their known layout available for bounds checks while keeping the
    /// symbolic load identity independent of the caller's memory snapshot.
    pub(in crate::kernel) fn with_block_without_derivation(
        mut self,
        block: impl Into<PointerBlock>,
        size: u32,
    ) -> Self {
        let diagnostic_base = self.clone();
        let block = block.into();
        std::sync::Arc::make_mut(&mut self.blocks).insert(block.clone(), CBlock::new(size));
        self.record_diagnostic_transform(
            "declare synthetic block",
            vec![diagnostic_base],
            vec![
                CValue::pointer(Pointer {
                    block: block.clone(),
                    offset: PointerOffsetTerm::Constant(0),
                }),
                CValue::Int32(size.into()),
            ],
        );
        self
    }

    /// Ends the lifetime of one automatic-storage object at a function exit
    /// or before a declaration is re-entered. The tombstone is semantic: it
    /// makes aliases to the old object invalid instead of merely making an
    /// eventual load unresolved because the block disappeared.
    pub(crate) fn without_local_block(&self, block: &PointerBlock) -> Self {
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
        std::sync::Arc::make_mut(&mut memory.forgotten)
            .ended_local_blocks
            .insert(block.clone());
        {
            let candidates = AliasCandidates::of_block(block);
            let heap = Arc::make_mut(&mut memory.heap);
            let CHeapMemory {
                native_record_inputs,
                native_record_input_origins,
                object_input_domains,
                scalar_input_domains,
                ..
            } = heap;
            // No facts are available at this lifetime boundary. Possible
            // aliases lose validity; only structural freshness/separation
            // preserves input promises, independently of byte permissions.
            candidates.retain_map(object_input_domains, |root, _| {
                root.block.proven_distinct(block)
            });
            candidates.retain_map(scalar_input_domains, |root, _| {
                root.block.proven_distinct(block)
            });
            candidates.retain_map(native_record_input_origins, |root, identities| {
                if root.block.proven_distinct(block) {
                    return true;
                }
                for identity in identities.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    native_record_inputs.remove(identity);
                }
                false
            });
        }
        // A later object is uninitialized until written; the tombstone
        // already refuses every access to this one.
        if own.any_entry(memory.heap.initialized.as_map(), |_, _| true) {
            std::sync::Arc::make_mut(&mut memory.heap)
                .initialized
                .forget_block(block);
        }
        record_c_memory_derivation(
            &mut memory,
            CMemoryDerivation::LocalLifetimeEnded {
                base,
                block: block.clone(),
            },
        );
        memory
    }

    /// Object input requirements assert a live referent independently of any
    /// byte permission. Retiring storage therefore drops every requirement it
    /// may reach, including an unowned input under another pointer spelling.
    /// Only complete byte separation preserves a requirement; address
    /// inequality or the absence of a definite alias is insufficient.
    fn retire_object_input_domains(
        &mut self,
        allocation: &Pointer,
        bytes: &Bitvector32Term,
        assumptions: &PureFactContext,
    ) {
        // Known block declarations currently come only from automatic objects
        // and fresh automatic by-value copies. A valid heap retirement cannot
        // end those objects; exact aliases are also removed by free's block
        // retirement. Heap/unknown input validity lives in these maps instead.
        // A future declared heap-object producer must supply allocation/lifetime
        // evidence here rather than relying on this automatic-storage boundary.
        let candidates = AliasCandidates::of_block(&allocation.block);
        let separate = |root: &Pointer, width: u32| {
            if root.blocks_proven_distinct(allocation) {
                return true;
            }
            if pointers_proven_equal_for_memory_resolution(allocation, root, assumptions) {
                return false;
            }
            if let Some(bytes) = bytes.as_const() {
                return crate::kernel::memory_provenance::write_access_is_disjoint_from_load(
                    allocation,
                    bytes,
                    root,
                    width,
                    assumptions,
                );
            }
            // Symbolic allocation extents still admit explicit complete-range
            // separation. Query only the selected block pair and composition
            // members, without scanning unrelated assumptions.
            let retired = CMemoryRange::new_with_element_width(
                allocation.clone(),
                0u32.into(),
                bytes.clone(),
                1,
            );
            let selected =
                CMemoryRange::new_with_element_width(root.clone(), 0u32.into(), 1u32.into(), width);
            // Keep symbolic extents exact: the general resource-containment
            // prover can search unrelated containment facts on a miss. This
            // bounded retirement rule conservatively drops other shapes.
            let covers = |held: &CMemoryRange, requested: &CMemoryRange| held == requested;
            if let Some((proposition, _, _)) = assumptions
                .memory_separation_candidates(&allocation.block, &root.block)
                .find(|(_, left, right)| {
                    ((covers(left, &retired) && covers(right, &selected))
                        || (covers(right, &retired) && covers(left, &selected)))
                        && !assumptions.memory_ranges_overlap_after_base_equality(left, right)
                })
            {
                crate::kernel::record_implicit_reasoning_provenance(assumptions, proposition);
                return true;
            }
            let Some((resources, _, _)) = assumptions.composition_separated_members(
                &allocation.block,
                &root.block,
                |held| covers(held, &retired),
                |held| covers(held, &selected),
                |left, right| !assumptions.memory_ranges_overlap_after_base_equality(left, right),
            ) else {
                return false;
            };
            crate::kernel::record_implicit_reasoning_provenance(
                assumptions,
                &Proposition::CResourceComposition(resources.clone()),
            );
            true
        };
        let heap = Arc::make_mut(&mut self.heap);
        candidates.retain_map(&mut heap.scalar_input_domains, |root, c_type| {
            separate(root, c_type.byte_width())
        });
        candidates.retain_map(&mut heap.object_input_domains, |root, layout| {
            separate(root, layout.size_bytes())
        });
        let selected = candidates
            .entries(&heap.native_record_input_origins)
            .map(|(root, identities)| (root.clone(), identities.clone()))
            .collect::<Vec<_>>();
        for (root, identities) in selected {
            let mut kept = identities.clone();
            for identity in identities.iter() {
                crate::instrumentation::record_deterministic_work(1);
                let keep = heap.native_record_inputs.get(identity).is_some_and(|row| {
                    let width = match &row.kind {
                        CNativeInputKind::Record { layout } => Some(layout.size_bytes()),
                        CNativeInputKind::RecordPrefix { layout, count } => count
                            .as_const()
                            .and_then(|count| u32::try_from(count).ok())
                            .and_then(|count| count.checked_mul(layout.size_bytes()))
                            .filter(|bytes| *bytes > 0),
                        CNativeInputKind::AllocatedScalar { bytes, .. } => bytes
                            .as_const()
                            .and_then(|bytes| u32::try_from(bytes).ok())
                            .filter(|bytes| *bytes > 0),
                        CNativeInputKind::TypedSlice {
                            element_type,
                            count,
                        }
                        | CNativeInputKind::TypedPrefix {
                            element_type,
                            count,
                            ..
                        } => count
                            .as_const()
                            .and_then(|count| u32::try_from(count).ok())
                            .and_then(|count| count.checked_mul(element_type.byte_width()))
                            .filter(|bytes| *bytes > 0),
                    };
                    root.block.proven_distinct(&allocation.block)
                        || width.is_some_and(|width| separate(&root, width))
                });
                if !keep {
                    heap.native_record_inputs.remove(identity);
                    kept.remove(identity);
                }
            }
            if kept.len() == 0 {
                heap.native_record_input_origins.remove(&root);
            } else {
                heap.native_record_input_origins.insert(root, kept);
            }
        }
    }

    pub(in crate::kernel) fn free_heap_block(
        mut self,
        pointer: &Pointer,
        assumptions: &PureFactContext,
    ) -> Result<Self, CInvalidFree> {
        // An aliased spelling of this allocation (a contract-returned pointer
        // proven equal to it, e.g. `ensures result == p`) is one address too.
        // Retiring through one identity has to retire it through both, else a
        // load through the other could read a stale cached cell or a stale
        // zeroed/uninitialized status after the free. Blocks proven distinct
        // from this allocation's own block keep everything.
        let mut aliased_blocks = BTreeSet::<PointerBlock>::new();
        for alias in assumptions.exact_pointer_aliases(pointer) {
            if alias.block != pointer.block && !alias.block.proven_distinct(&pointer.block) {
                aliased_blocks.insert(alias.block.clone());
            }
        }
        if self.heap.deallocated_allocations.contains_key(pointer) {
            return Err(CInvalidFree::DoubleFree);
        }
        // Every heap entry and cell this free can retire is in a block not
        // proven distinct from the freed pointer's: `heap_allocation_may_
        // contain_pointer` answers `false` for every other block, and the
        // aliased spellings above are not proven distinct by construction.
        let candidates = AliasCandidates::of_block(&pointer.block);
        let Some(bytes) = std::sync::Arc::make_mut(&mut self.heap)
            .live_allocations
            .remove(pointer)
        else {
            return Err(
                if candidates.any_entry(&self.heap.live_allocations, |base, _| {
                    heap_allocation_may_contain_pointer(base, pointer, assumptions)
                }) {
                    CInvalidFree::InteriorPointer
                } else {
                    CInvalidFree::NonHeapPointer
                },
            );
        };
        let base = Some(intern_derivation_base(&mut self));
        if pointer.block != PointerBlock::ExternalArgument {
            std::sync::Arc::make_mut(&mut self.blocks).remove(&pointer.block);
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
        retired.insert(pointer.block.clone());
        let retired_key = |base: &Pointer| {
            retired.contains(&base.block) && base.offset == pointer.offset
                || heap_allocation_may_contain_pointer(base, pointer, assumptions)
        };
        let heap = std::sync::Arc::make_mut(&mut self.heap);
        let freed_within = |base: &Pointer| retired_key(base);
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
        self.retire_object_input_domains(pointer, &bytes, assumptions);
        // Cached values go with the storage, union views as well as cells:
        // nothing may answer a load of freed bytes, under any spelling.
        self.forget_cached_values(
            ForgetScope::candidates(&candidates),
            |cell, _| {
                if aliased_blocks.contains(&cell.block) || freed_within(cell) {
                    CachedValueFate::Retired
                } else {
                    CachedValueFate::Kept
                }
            },
            ask_every_slot,
        );
        if let Some(base) = base {
            record_c_memory_derivation(
                &mut self,
                CMemoryDerivation::HeapFreed {
                    base,
                    allocation_base: pointer.clone(),
                    bytes: bytes.clone(),
                },
            );
        }
        Ok(self)
    }

    pub(in crate::kernel) fn live_heap_block_size(
        &self,
        pointer: &Pointer,
    ) -> Option<&Bitvector32Term> {
        self.heap.live_allocations.get(pointer)
    }

    pub(crate) fn is_live_heap_address(
        &self,
        pointer: &Pointer,
        assumptions: &PureFactContext,
    ) -> bool {
        // An allocation based in a block proven distinct from the pointer's
        // never contains it, so only the candidate entries are asked.
        self.heap.live_allocations.contains_key(pointer)
            || AliasCandidates::of_block(&pointer.block)
                .any_entry(&self.heap.live_allocations, |base, _| {
                    heap_allocation_may_contain_pointer(base, pointer, assumptions)
                })
    }

    pub(in crate::kernel) fn heap_live_allocation_bases(&self) -> impl Iterator<Item = &Pointer> {
        self.heap.live_allocations.keys()
    }

    pub(in crate::kernel) fn is_uninitialized_heap_address(
        &self,
        pointer: &Pointer,
        byte_width: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        let candidates = AliasCandidates::of_block(&pointer.block);
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
        mutable_ranges: &[CMemoryRange],
        assumptions: &PureFactContext,
    ) {
        if mutable_ranges.is_empty() {
            return;
        }
        let written = |base: &Pointer| {
            mutable_ranges
                .iter()
                .any(|range| heap_allocation_may_contain_pointer(base, range.base(), assumptions))
        };
        // An allocation based in a block proven distinct from every range
        // base contains none of them.
        let candidates =
            AliasCandidates::of_blocks(mutable_ranges.iter().map(|range| &range.base().block));
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
        pointer: &Pointer,
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
                let at = |offset: i64| Pointer {
                    block: pointer.block.clone(),
                    offset: PointerOffsetTerm::Constant(offset),
                };
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
                                    value,
                                ),
                            )
                            })
                        });
                cell_overlaps
                    || self.cells.runs_in_block(&pointer.block).any(|run| {
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
                let candidates = AliasCandidates::of_block(&pointer.block);
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
        pointer: &Pointer,
        byte_width: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        // A zeroed allocation reads as zero only where nothing was stored
        // over the bytes the load reads; a store at another address can
        // still cover some of them.
        if self.stored_bytes_overlap(pointer, byte_width) {
            return false;
        }
        let candidates = AliasCandidates::of_block(&pointer.block);
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
        pointer: &Pointer,
        assumptions: &PureFactContext,
    ) -> bool {
        AliasCandidates::of_block(&pointer.block)
            .any_entry(&self.heap.deallocated_allocations, |base, _| {
                heap_allocation_may_contain_pointer(base, pointer, assumptions)
            })
    }

    /// Whether no allocation has been freed in this snapshot.
    pub(in crate::kernel) fn heap_has_no_deallocations(&self) -> bool {
        self.heap.deallocated_allocations.is_empty()
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
        pointer: &Pointer,
        assumptions: &PureFactContext,
    ) -> Option<Pointer> {
        if self.heap.deallocated_allocations.is_empty() {
            return None;
        }
        let candidates = AliasCandidates::only_block(&pointer.block);
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
        base: Pointer,
        bytes: impl Into<Bitvector32Term>,
    ) -> Option<Self> {
        let bytes = bytes.into();
        if bytes.as_const() == Some(0) || self.heap.deallocated_allocations.contains_key(&base) {
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
                    record_c_memory_derivation(
                        &mut self,
                        CMemoryDerivation::ContractAllocationClaimsChanged { base: prior },
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
        base: &Pointer,
        bytes: &Bitvector32Term,
        assumptions: &PureFactContext,
    ) -> Self {
        let prior = intern_derivation_base(&mut self);
        let mut retired_blocks = BTreeSet::from([base.block.clone()]);
        for alias in assumptions.exact_pointer_aliases(base) {
            if !alias.block.proven_distinct(&base.block) {
                retired_blocks.insert(alias.block.clone());
            }
        }
        let retired_claim = |candidate: &Pointer| {
            heap_allocation_may_contain_pointer(candidate, base, assumptions)
                || pointers_proven_equal_for_memory_resolution(candidate, base, assumptions)
        };
        // A symbolic alias block can hold cells at interior offsets. As at a
        // definite free, dropping that block's cached cells is conservative:
        // an undecided contract can replace the allocation entirely.
        let retired_cell = |candidate: &Pointer| {
            retired_blocks.contains(&candidate.block) || retired_claim(candidate)
        };

        // Neither predicate holds in a block proven distinct from the base's,
        // and the retired alias blocks are not proven distinct from it.
        let candidates = AliasCandidates::of_block(&base.block);
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
        self.retire_object_input_domains(base, bytes, assumptions);
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
            if *block != PointerBlock::ExternalArgument {
                std::sync::Arc::make_mut(&mut self.blocks).remove(block);
            }
        }
        // Losing an allocation's cached knowledge can otherwise re-intern as
        // an older empty snapshot and drop this safety-critical edge. A
        // retirement inside its own call's havoc keeps that havoc's mark
        // instead: see `retirement_keeps_its_call_havocs_forget_mark`.
        use crate::kernel::resource_tracker::cell_source::retirement_keeps_its_call_havocs_forget_mark;
        if !retirement_keeps_its_call_havocs_forget_mark(&prior, base, bytes) {
            self.mark_forgotten_from(&prior);
        }
        record_c_memory_derivation(
            &mut self,
            CMemoryDerivation::ContractAllocationRetired {
                base: prior,
                allocation_base: base.clone(),
                bytes: bytes.clone(),
            },
        );
        self
    }

    pub(in crate::kernel) fn with_pending_allocated_scalar(
        self,
        base: Pointer,
        bytes: Bitvector32Term,
        zeroed: bool,
        element_type: CType,
        identity: Variable,
    ) -> Result<Self, String> {
        if base != Pointer::symbolic(identity)
            || !matches!(
                element_type,
                CType::Int32 | CType::Int64 | CType::UInt32 | CType::UInt8
            )
            || self
                .heap
                .native_record_inputs
                .contains_key(&CNativeInputIdentity::Unresolved(identity))
        {
            return Err(
                "allocated scalar requires an exact fresh scalar allocation producer".into(),
            );
        }
        let extent = Self::allocated_byte_extent(&bytes)
            .ok_or("allocated scalar byte extent lacks a native observation")?;
        let mut next = self.with_pending_heap_allocation(base.clone(), bytes, zeroed);
        let metadata_base = intern_derivation_base(&mut next);
        let origin = CPointerValue::new(base.clone(), element_type.pointer_to().unwrap())
            .with_designation(PointerDesignation::Unresolved(identity));
        let key = CNativeInputIdentity::Unresolved(identity);
        let heap = Arc::make_mut(&mut next.heap);
        heap.native_record_inputs.insert(
            key.clone(),
            CNativeRecordInput {
                origin,
                kind: CNativeInputKind::AllocatedScalar {
                    element_type,
                    bytes: extent,
                },
            },
        );
        let mut identities = SnapshotSet::default();
        identities.insert(key);
        heap.native_record_input_origins.insert(base, identities);
        record_c_memory_derivation(
            &mut next,
            CMemoryDerivation::CellsForgotten {
                base: metadata_base,
            },
        );
        Ok(next)
    }

    pub(in crate::kernel) fn with_pending_heap_allocation(
        mut self,
        base: Pointer,
        bytes: Bitvector32Term,
        zeroed: bool,
    ) -> Self {
        let prior = Some(intern_derivation_base(&mut self));
        std::sync::Arc::make_mut(&mut self.heap)
            .pending_allocations
            .insert(base.clone(), bytes.clone());
        if zeroed {
            std::sync::Arc::make_mut(&mut self.heap)
                .zeroed_pending_allocations
                .insert(base.clone());
        }
        if let Some(prior) = prior {
            record_c_memory_derivation(
                &mut self,
                CMemoryDerivation::HeapAllocationPending {
                    base: prior,
                    allocation_base: base,
                    bytes,
                },
            );
        }
        self
    }

    pub(in crate::kernel) fn with_pending_heap_reallocation(
        mut self,
        base: Pointer,
        old_pointer: CPointerValue,
        old_bytes: Bitvector32Term,
        zeroed_prefix: Option<Bitvector32Term>,
        copied_cells: Vec<(PointerOffsetTerm, CValue)>,
        initialized_prefix: Vec<(i64, u32)>,
    ) -> Self {
        let diagnostic_base = self.clone();
        std::sync::Arc::make_mut(&mut self.heap)
            .pending_reallocations
            .insert(
                base.clone(),
                CPendingReallocation {
                    old_pointer: old_pointer.clone(),
                    old_bytes: old_bytes.clone(),
                    zeroed_prefix,
                    copied_cells,
                    initialized_prefix,
                },
            );
        self.record_diagnostic_transform(
            "register pending reallocation",
            vec![diagnostic_base],
            vec![
                CValue::pointer(base.clone()),
                CValue::Pointer(old_pointer.clone()),
                CValue::Int32(old_bytes.clone()),
            ],
        );
        self
    }

    /// The runs of constant byte offsets of `block` the initialization
    /// record holds, ascending, as start and length. Costs the entries of
    /// the one block.
    pub(in crate::kernel) fn initialized_runs_in_block(
        &self,
        block: &PointerBlock,
    ) -> Vec<(i64, u32)> {
        self.heap.initialized.constant_runs_in_block(block)
    }

    /// Whether execution still owns the unresolved success/failure choice of
    /// a fresh heap allocation. Proof-frontier branch selection uses this
    /// read-only query to avoid duplicating that independent path split.
    pub(crate) fn has_pending_heap_allocation(&self) -> bool {
        !self.heap.pending_allocations.is_empty()
    }

    pub(in crate::kernel) fn heap_identity_in_use(&self, identity: u64) -> bool {
        self.blocks.contains_key(&PointerBlock::Heap(identity))
            || self
                .heap
                .deallocated_allocations
                .keys()
                .any(|base| base.block == PointerBlock::Heap(identity))
            || self
                .heap
                .pending_allocations
                .keys()
                .any(|base| base.block == PointerBlock::Symbolic(Variable(identity)))
    }

    pub(in crate::kernel) fn resolve_pending_heap_allocation(
        mut self,
        base: &Pointer,
        succeeds: bool,
    ) -> Option<(Self, Bitvector32Term, Pointer)> {
        let prior = Some(intern_derivation_base(&mut self));
        let bytes = std::sync::Arc::make_mut(&mut self.heap)
            .pending_allocations
            .remove(base)?;
        let zeroed = std::sync::Arc::make_mut(&mut self.heap)
            .zeroed_pending_allocations
            .remove(base);
        let resolved_base = if succeeds {
            let PointerBlock::Symbolic(variable) = base.block else {
                return None;
            };
            Pointer {
                block: PointerBlock::Heap(variable.0),
                offset: PointerOffsetTerm::Constant(0),
            }
        } else {
            Pointer::null()
        };
        if let PointerBlock::Symbolic(identity) = base.block {
            let key = CNativeInputIdentity::Unresolved(identity);
            if self.heap.native_record_inputs.get(&key).is_some_and(|row| {
                matches!(row.kind, CNativeInputKind::AllocatedScalar { .. })
                    && row.origin.pointer() == base
            }) {
                let heap = Arc::make_mut(&mut self.heap);
                let mut row = heap.native_record_inputs.remove(&key).unwrap();
                heap.native_record_input_origins.remove(base);
                if succeeds {
                    row.origin.replace_pointer(resolved_base.clone());
                    let mut identities = SnapshotSet::default();
                    identities.insert(key.clone());
                    heap.native_record_input_origins
                        .insert(resolved_base.clone(), identities);
                    heap.native_record_inputs.insert(key, row);
                }
            }
        }
        if succeeds {
            std::sync::Arc::make_mut(&mut self.blocks).insert(
                resolved_base.block.clone(),
                CBlock::with_symbolic_size(bytes.clone()),
            );
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
                record_c_memory_derivation(
                    &mut self,
                    CMemoryDerivation::HeapAllocated {
                        base: prior,
                        block: resolved_base.block.clone(),
                        bytes: bytes.clone(),
                    },
                );
            }
        } else if let Some(prior) = prior {
            record_c_memory_derivation(
                &mut self,
                CMemoryDerivation::HeapAllocationFailed { base: prior },
            );
        }
        Some((self, bytes, resolved_base))
    }

    pub(in crate::kernel) fn resolve_pending_heap_reallocation(
        mut self,
        base: &Pointer,
        succeeds: bool,
        assumptions: &PureFactContext,
    ) -> Option<(Self, Bitvector32Term, Pointer, CPendingReallocation)> {
        let diagnostic_base = self.clone();
        let pending = std::sync::Arc::make_mut(&mut self.heap)
            .pending_reallocations
            .remove(base)?;
        self.record_diagnostic_transform(
            "consume pending reallocation",
            vec![diagnostic_base.clone()],
            vec![CValue::pointer(base.clone())],
        );
        let pending_scalar_row = if let PointerBlock::Symbolic(identity) = base.block {
            let key = CNativeInputIdentity::Unresolved(identity);
            self.heap
                .native_record_inputs
                .get(&key)
                .filter(|row| {
                    row.origin.pointer() == base
                        && matches!(row.kind, CNativeInputKind::AllocatedScalar { .. })
                })
                .cloned()
                .map(|row| (key, row))
        } else {
            None
        };
        let (mut memory, bytes, resolved_base) = if succeeds {
            self = self
                .free_heap_block(&pending.old_pointer, assumptions)
                .ok()?;
            // The fresh pending producer remains independent of the old
            // allocation. Free's conservative alias retirement may drop its
            // not-yet-resolved symbolic row; restore that exact producer only.
            if let Some((key, row)) = pending_scalar_row {
                let heap = Arc::make_mut(&mut self.heap);
                heap.native_record_inputs.insert(key.clone(), row);
                let mut identities = SnapshotSet::default();
                identities.insert(key);
                heap.native_record_input_origins
                    .insert(base.clone(), identities);
            }
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
                    .zip(bytes.as_const())
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
                vec![CValue::pointer(resolved_base.clone())],
            );
            for (offset, value) in &pending.copied_cells {
                memory = memory.store(
                    Pointer {
                        block: resolved_base.block.clone(),
                        offset: offset.clone(),
                    },
                    value.clone(),
                );
            }
            // Bytes the old block had initialized keep that, in the new
            // block, where no cached cell carried their value across.
            for (start, length) in &pending.initialized_prefix {
                memory = memory.with_initialized_object(
                    &Pointer {
                        block: resolved_base.block.clone(),
                        offset: PointerOffsetTerm::Constant(*start),
                    },
                    *length,
                );
            }
        }
        Some((memory, bytes, resolved_base, pending))
    }

    pub(in crate::kernel) fn with_loop_memory_havoc_preserving_loans(
        mut self,
        variable: Variable,
        preserved_blocks: &BTreeSet<PointerBlock>,
        mutable_ranges: Option<&[CMemoryRange]>,
        ledger: Option<&crate::kernel::loans::LoanLedger>,
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
        self.forget_loan_unprotected_values(preserved_blocks, ledger, &[]);
        // The body may also have written bytes no value was cached for, and
        // a zero reading answers for exactly those.
        match mutable_ranges {
            Some(ranges) => {
                self.forget_zero_readings_under(ranges.iter().map(|range| &range.base().block))
            }
            None => self.forget_every_zero_reading(),
        }
        std::sync::Arc::make_mut(&mut self.blocks).insert(
            format!("havoc:{}", variable.0).into(),
            CBlock::new(mutable_ranges.map_or(0, memory_havoc_write_set_fingerprint)),
        );
        if let Some(base) = base {
            record_c_memory_derivation(
                &mut self,
                CMemoryDerivation::LoopHavoc {
                    base,
                    variable,
                    mutable_ranges: mutable_ranges.map(|ranges| ranges.to_vec()),
                },
            );
        }
        self
    }

    /// Forgets every cached value nothing protects from a write through an
    /// arbitrary reachable pointer: the one rule of the loop head and of the
    /// interface join ([`loan_preserving_havoc_keeps_cell`]), asked of cells
    /// and typed union views alike. Whole-map by design, unlike the
    /// per-access rules that visit only `AliasCandidates`: the work is the
    /// values dropped plus the ones something keeps.
    ///
    /// `agreeing` are the arms of a join, and empty at a loop head. A cell
    /// every arm caches with the same value is a reading each arm's memory
    /// already gives, so it is a reading of their join and stays; so does a
    /// run every arm holds unchanged. Only plain cells stay this way: a typed
    /// union view, and a cell a union overlays, go by the loan rule alone.
    /// The work is unchanged: one lookup per arm for each value visited.
    fn forget_loan_unprotected_values(
        &mut self,
        preserved_blocks: &BTreeSet<PointerBlock>,
        ledger: Option<&crate::kernel::loans::LoanLedger>,
        agreeing: &[&CMemory],
    ) {
        let union_widths = union_overlay_widths(self);
        let arm_overlays = agreeing
            .iter()
            .map(|memory| union_overlay_widths(memory))
            .collect::<Vec<_>>();
        self.forget_cached_values(
            ForgetScope::Everywhere,
            |pointer, value| {
                // A view is asked by its own width; a cell by the widest
                // overlay at its address as well, so the loan question
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
                                && memory.cells.concrete().get(pointer) == Some(cell)
                        })
                {
                    return CachedValueFate::Kept;
                }
                if loan_preserving_havoc_keeps_cell(
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
                loan_preserving_havoc_keeps_run(run, preserved_blocks, ledger)
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
        heap.zeroed_allocations = SnapshotSet::new();
        heap.zeroed_prefix_allocations = SnapshotMap::new();
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
    /// snapshot is a provenance barrier instead: no load from before the
    /// branch is transported across it. What survives is a value every arm
    /// still caches for the same cell, kept as a cell of the joined snapshot,
    /// and whatever the interface states as a fact.
    #[cfg(test)]
    pub(in crate::kernel) fn with_interface_memory_havoc(
        self,
        variable: Variable,
        preserved_blocks: &BTreeSet<PointerBlock>,
        sibling_memories: &[&CMemory],
    ) -> Result<Self, String> {
        self.with_interface_memory_havoc_preserving_loans(
            variable,
            preserved_blocks,
            sibling_memories,
            None,
        )
    }

    pub(in crate::kernel) fn with_interface_memory_havoc_preserving_loans(
        mut self,
        variable: Variable,
        preserved_blocks: &BTreeSet<PointerBlock>,
        sibling_memories: &[&CMemory],
        ledger: Option<&crate::kernel::loans::LoanLedger>,
    ) -> Result<Self, String> {
        let mut incoming = std::iter::once(&self)
            .chain(sibling_memories.iter().copied())
            .map(intern_c_memory_ref)
            .collect::<Vec<_>>();
        incoming.sort_by_key(SharedCMemory::arena_id);
        incoming.dedup();
        let Some(first) = sibling_memories.first() else {
            return Err("an interface memory join has no sibling states".to_string());
        };

        // Every merge below starts from the first arm's collection and
        // visits only the entries on which another arm differs from it. The
        // arms share what neither touched, so the work is their changes.
        let others = &sibling_memories[1..];
        let blocks = union_of_arm_maps(&first.blocks, others.iter().map(|memory| &*memory.blocks))
            .map_err(|block| {
                format!("interface arms disagree on the size of memory block {block:?}")
            })?;
        let ended_local_blocks = union_of_arm_sets(
            &first.forgotten.ended_local_blocks,
            others
                .iter()
                .map(|memory| &memory.forgotten.ended_local_blocks),
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
        let pending_reallocations = first.heap.pending_reallocations.clone();
        if sibling_memories
            .iter()
            .any(|memory| memory.heap.pending_reallocations != pending_reallocations)
        {
            return Err("interface arms disagree on pending heap reallocations".to_string());
        }

        let uninitialized_objects = union_of_arm_maps(
            &first.heap.uninitialized_objects,
            others
                .iter()
                .map(|memory| &memory.heap.uninitialized_objects),
        )
        .map_err(|base| {
            format!("interface arms disagree on unwritten object extent at {base:?}")
        })?;
        let scalar_input_domains = first.heap.scalar_input_domains.clone();
        if others
            .iter()
            .any(|memory| memory.heap.scalar_input_domains != scalar_input_domains)
        {
            return Err("interface arms disagree on scalar input domains".into());
        }
        let object_input_domains = first.heap.object_input_domains.clone();
        if others
            .iter()
            .any(|memory| memory.heap.object_input_domains != object_input_domains)
        {
            return Err("interface arms disagree on object input domains".into());
        }

        let native_record_inputs = first.heap.native_record_inputs.clone();
        let native_record_input_origins = first.heap.native_record_input_origins.clone();
        if others.iter().any(|memory| {
            memory.heap.native_record_inputs != native_record_inputs
                || memory.heap.native_record_input_origins != native_record_input_origins
        }) {
            return Err("interface arms disagree on native record input identities".into());
        }

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
        let arm_initialized = |memory: &CMemory| {
            let mut record = memory.heap.initialized.clone();
            let mut visited = 0usize;
            for (pointer, value) in local_block_entries(memory.cells.logical()) {
                visited += 1;
                if !preserved_blocks.contains(&pointer.block) {
                    record.record(pointer, value.byte_width());
                }
            }
            for ((pointer, c_type), _) in local_block_entries(&memory.union_cells) {
                visited += 1;
                if !preserved_blocks.contains(&pointer.block) {
                    record.record(pointer, c_type.byte_width());
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
        let mut zeroed_prefix_allocations = SnapshotMap::new();
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
                        memory.heap.live_allocations.get(base).cloned()
                    } else {
                        memory.heap.zeroed_prefix_allocations.get(base).cloned()
                    }
                })
                .collect::<Option<Vec<_>>>();
            let Some(prefixes) = prefixes else {
                continue;
            };
            let Some(prefixes) = prefixes
                .iter()
                .map(Bitvector32Term::as_const)
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
                    Bitvector32Term::Constant(
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
        // arms agree on, and a cell under one goes with it, so a snapshot
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
                        loan_preserving_havoc_keeps_cell(
                            pointer,
                            value.byte_width(),
                            preserved_blocks,
                            ledger,
                        )
                    },
                    |run| loan_preserving_havoc_keeps_run(run, preserved_blocks, ledger),
                ),
            )
        } else {
            self.forget_loan_unprotected_values(preserved_blocks, ledger, sibling_memories);
            None
        };
        // A zero reading is kept only where every arm has it, but an arm can
        // have it beside a value it wrote over the zeros, and that value is
        // forgotten here. So a reading goes wherever *any* arm caches a value
        // the join forgets, which is also what keeps every arm's abstraction
        // the same one.
        let forgotten_value_blocks = |memory: &CMemory| {
            if zeroed_allocations.len() == 0 && zeroed_prefix_allocations.is_empty() {
                return BTreeSet::new();
            }
            let mut blocks = BTreeSet::new();
            let mut visited = 0usize;
            let union_widths = union_overlay_widths(memory);
            for (pointer, value) in memory.cells.logical().iter() {
                visited += 1;
                if !loan_preserving_havoc_keeps_cell(
                    pointer,
                    value
                        .byte_width()
                        .max(union_widths.get(pointer).copied().unwrap_or(0)),
                    preserved_blocks,
                    ledger,
                ) {
                    blocks.insert(pointer.block.clone());
                }
            }
            for ((pointer, c_type), _) in memory.union_cells.iter() {
                visited += 1;
                if !loan_preserving_havoc_keeps_cell(
                    pointer,
                    c_type.byte_width(),
                    preserved_blocks,
                    ledger,
                ) {
                    blocks.insert(pointer.block.clone());
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
        blocks.insert(format!("havoc:{}", variable.0).into(), CBlock::new(0));
        self.blocks = std::sync::Arc::new(blocks);
        let forgotten = std::sync::Arc::make_mut(&mut self.forgotten);
        forgotten.ended_local_blocks = ended_local_blocks;
        // A forget mark says this snapshot is some earlier one with cached
        // values dropped and the memory itself unchanged. The joined memory
        // is no arm's memory: it is their abstraction, named by its own
        // fresh havoc block above. Keeping an arm's mark would also make the
        // abstraction depend on which arm it was computed from, so arms that
        // forgot from different snapshots on the way could never rejoin.
        forgotten.forgotten_from = None;
        forgotten.join_inputs = incoming
            .iter()
            .map(|memory| ForgottenFrom {
                content_hash: c_memory_content_hash(memory.memory()),
                arena_id: memory.arena_id(),
            })
            .collect();
        self.heap = std::sync::Arc::new(CHeapMemory {
            live_allocations,
            deallocated_allocations,
            pending_allocations,
            uninitialized_allocations,
            uninitialized_objects,
            object_input_domains,
            scalar_input_domains,
            native_record_inputs,
            native_record_input_origins,
            initialized,
            zeroed_allocations,
            zeroed_prefix_allocations,
            zeroed_pending_allocations,
            pending_reallocations,
        });
        self.forget_zero_readings_under(forgotten_blocks.iter());
        record_c_memory_derivation(
            &mut self,
            CMemoryDerivation::BranchJoin {
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
        mutable_ranges: &[CMemoryRange],
        assumptions: &PureFactContext,
    ) -> Self {
        self.with_memory_havoc(variable, mutable_ranges, assumptions, None, false)
    }

    pub(in crate::kernel) fn with_call_memory_havoc(
        self,
        variable: Variable,
        mutable_ranges: &[CMemoryRange],
        assumptions: &PureFactContext,
        kept: Option<&CallKeptOwnership>,
    ) -> Self {
        self.with_memory_havoc(variable, mutable_ranges, assumptions, kept, true)
    }

    fn with_memory_havoc(
        mut self,
        variable: Variable,
        mutable_ranges: &[CMemoryRange],
        assumptions: &PureFactContext,
        kept: Option<&CallKeptOwnership>,
        preserve_local_slots: bool,
    ) -> Self {
        let base = Some(intern_derivation_base(&mut self));
        let mut flat_hits = Vec::new();
        let candidates = call_havoc_candidates(mutable_ranges);
        // Cells and typed union views by one rule: a view is the
        // authoritative answer to an exact typed load, so one the callee may
        // have overwritten goes exactly as a cell does
        // (`mdtests/call_havoc_drops_a_union_member_view.md`). A callee can
        // only initialize more, so the automatic values that go stay
        // initialized.
        self.forget_cached_values(
            ForgetScope::candidates(&candidates),
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
                CallHavocCellRule::KeptByCaller(range) => {
                    flat_hits.push(range);
                    CachedValueFate::Forgotten
                }
                CallHavocCellRule::Dropped => CachedValueFate::Forgotten,
            },
            ask_every_slot,
        );
        let kept_ranges = call_havoc_kept_ranges(kept, flat_hits, &candidates);
        self.forget_zeroed_allocations_written_by(mutable_ranges, assumptions);
        std::sync::Arc::make_mut(&mut self.blocks).insert(
            format!("call-havoc:{}", variable.0).into(),
            CBlock::new(memory_havoc_write_set_fingerprint(mutable_ranges)),
        );
        // Keep the legacy marker's semantic shape and add a collision-free
        // structural key for the checked write set, and for the memory the
        // caller kept owning. This key is intentionally not named as a havoc
        // marker: canonical load snapshots must continue to treat the
        // call-havoc edge as the only global memory barrier.
        std::sync::Arc::make_mut(&mut self.blocks).insert(
            call_write_set_marker(variable.0, mutable_ranges, kept_ranges.as_ref()),
            CBlock::new(0),
        );
        if let Some(base) = base {
            record_c_memory_derivation(
                &mut self,
                CMemoryDerivation::CallHavoc {
                    base,
                    variable,
                    mutable_ranges: mutable_ranges.to_vec(),
                    kept_by_caller: kept_ranges,
                },
            );
        }
        self
    }

    /// Checks that `self` is exactly the cell-and-marker result produced by a
    /// call havoc from `before`. This is deliberately a structural producer
    /// check rather than a second alias approximation: erased cells are
    /// accepted only when the endpoint has the call-havoc shape and the same
    /// conservative retention rule as [`Self::with_call_memory_havoc`].
    pub(in crate::kernel) fn matches_call_memory_havoc_result(
        &self,
        before: &Self,
        mutable_ranges: &[CMemoryRange],
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
            let SnapshotMapChange::Added(block) = change else {
                return false;
            };
            let Some(contents) = self.blocks.get(block) else {
                return false;
            };
            added_blocks.push((block, contents));
        }
        let Some((marker, marker_block)) = added_blocks
            .iter()
            .find(|(block, _)| block.starts_with("call-havoc:"))
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
        // walks only the paths the two snapshots do not share.
        let candidates = call_havoc_candidates(mutable_ranges);
        let mut visited = 0usize;
        let mut flat_hits = Vec::new();
        let mut dropped_cells = Vec::new();
        let mut dropped_initialized = Vec::new();
        for (pointer, value) in before.cells.candidate_logical_entries(&candidates) {
            visited += 1;
            match call_havoc_keeps_cell(&pointer, &value, mutable_ranges, assumptions, kept, true) {
                CallHavocCellRule::Separate => {}
                CallHavocCellRule::KeptByCaller(range) => {
                    flat_hits.push(range);
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
            match call_havoc_keeps_cell(&key.0, value, mutable_ranges, assumptions, kept, true) {
                CallHavocCellRule::Separate => {}
                CallHavocCellRule::KeptByCaller(range) => {
                    flat_hits.push(range);
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
        // a dropped value or the write set ([`CMemory::forget_cached_values`]).
        let mut expected = before.clone();
        expected.record_dropped_initialized_cells(&dropped_initialized);
        expected.forget_zero_readings_under(
            dropped_initialized
                .iter()
                .map(|(pointer, _)| &pointer.block),
        );
        expected.forget_zeroed_allocations_written_by(mutable_ranges, assumptions);
        if !self.heap.eq_relative_to(&expected.heap, &before.heap) {
            return false;
        }
        let kept_ranges = call_havoc_kept_ranges(kept, flat_hits, &candidates);
        let write_set_marker =
            call_write_set_marker(variable, mutable_ranges, kept_ranges.as_ref());
        if added_blocks.len() != 2
            || **marker_block != CBlock::new(memory_havoc_write_set_fingerprint(mutable_ranges))
            || self.blocks.get(&write_set_marker) != Some(&CBlock::new(0))
        {
            return false;
        }
        self.cells.is_without(&before.cells, &dropped_cells)
            && self
                .union_cells
                .is_without(&before.union_cells, &dropped_union_cells)
    }

    /// Seeds the cells of elements `first..count` at `base`,
    /// `base + element_width`, …: each one the load of its own element in
    /// `source`, typed as `element_type` ([`cell_run_value`]). This is exactly
    /// `store` of each such value in element order, skipping every element
    /// that already holds a cell, and
    /// it costs the same whatever `count` is: the cells are one [`CellRun`]
    /// and the stores one `CellsSeeded` edge.
    ///
    /// Two things a store does that a run does not represent are refused
    /// rather than approximated: displacing typed union views (the snapshot
    /// holds some) and marking a live heap cell initialized (an allocation
    /// may hold the range). Those fall back to the stores themselves.
    // Kept for checking the store-equivalent run representation in kernel tests.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn with_seeded_cells(
        mut self,
        base: Pointer,
        element_width: u32,
        element_type: CType,
        first: u32,
        count: u32,
        source: SharedCMemory,
    ) -> Self {
        if first >= count {
            return self;
        }
        if !self.run_can_stand_for_cells_at(&base) {
            let run = CellRun::new(
                base,
                element_width,
                element_type,
                count,
                source,
                IndexIntervals::default(),
            );
            for index in first..count {
                let pointer = run.slot_pointer(index);
                if !matches!(self.load(&pointer), CExpressionOutcome::Value(_)) {
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

    /// Name initialized universal input cells without treating proof-entry
    /// resource materialization as a C write. An output footprint marked
    /// unwritten stays unwritten, independently of its ownership/liveness.
    #[allow(clippy::too_many_arguments)]
    #[cfg(test)]
    pub(crate) fn with_proof_entry_cells(
        self,
        base: Pointer,
        element_width: u32,
        element_type: CType,
        first: u32,
        count: u32,
        source: SharedCMemory,
    ) -> Self {
        self.with_proof_entry_cells_under(
            base,
            element_width,
            element_type,
            first,
            count,
            source,
            &PureFactContext::new(),
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn with_proof_entry_cells_under(
        self,
        base: Pointer,
        element_width: u32,
        element_type: CType,
        first: u32,
        count: u32,
        source: SharedCMemory,
        assumptions: &PureFactContext,
    ) -> Self {
        if first >= count {
            return self;
        }
        let Some(start) = first.checked_mul(element_width) else {
            return self;
        };
        let Some(bytes) = (count - first).checked_mul(element_width) else {
            return self;
        };
        if self.may_read_uninitialized_object_under(
            &base.offset_by_bytes(start),
            bytes,
            assumptions,
        ) {
            return self;
        }
        // The full run has already been checked separate from raw outputs.
        // Their presence elsewhere must not force enumeration of this input.
        if !base.block.starts_with("local:")
            && !matches!(base.block, PointerBlock::Heap(_))
            && self.union_cells.is_empty()
            && !AliasCandidates::of_block(&base.block)
                .any_entry(&self.heap.live_allocations, |_, _| true)
        {
            self.with_proof_entry_run(base, element_width, element_type, first, count, source)
        } else {
            let mut memory = self;
            let run = CellRun::new(
                base,
                element_width,
                element_type,
                count,
                source,
                IndexIntervals::default(),
            );
            for index in first..count {
                let pointer = run.slot_pointer(index);
                if !matches!(memory.load(&pointer), CExpressionOutcome::Value(_)) {
                    memory =
                        memory.materialize_named_cell_under(pointer, run.value(index), assumptions);
                }
            }
            memory
        }
    }

    /// Install logical input names using only cells and runs on their spelled
    /// span. The caller has checked separation from every raw output.
    #[allow(clippy::too_many_arguments)]
    fn with_proof_entry_run(
        mut self,
        base: Pointer,
        element_width: u32,
        element_type: CType,
        first: u32,
        count: u32,
        source: SharedCMemory,
    ) -> Self {
        let mut holes = IndexIntervals::default();
        holes.insert_range(0, first);
        let probe = CellRun::new(
            base.clone(),
            element_width,
            element_type,
            count,
            source,
            holes,
        );
        let start = base.offset_by_bytes(first * element_width);
        let bytes = (count - first) * element_width;
        let selected = CellRun::new(
            start.clone(),
            element_width,
            element_type,
            count - first,
            probe.source().clone(),
            IndexIntervals::default(),
        );
        let mut holes = probe.holes().clone();
        for (pointer, _) in self.cells.concrete_region_candidates(&start, bytes) {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(index) = probe.slot_index(pointer) {
                holes.insert(index);
            }
        }
        if !probe.has_canonical_slot_base() {
            // The range index spells canonical offsets. A noncanonical base
            // can preserve exceptional spellings at zero or cancelling
            // shifts, so check this selected span's exact concrete slots.
            for index in first..count {
                crate::instrumentation::record_deterministic_work(1);
                if self
                    .cells
                    .concrete()
                    .contains_key(&probe.slot_pointer(index))
                {
                    holes.insert(index);
                }
            }
        }
        for run in self.cells.runs_in_slot_span_of(&selected) {
            if run.element_width() == element_width
                && (run.base() == &base
                    || (run.has_canonical_slot_base() && probe.has_canonical_slot_base()))
                && let Some(delta) =
                    run.base()
                        .exact_element_delta_from_base(&base, element_width, None)
                && delta.is_constant()
            {
                for (low, high) in run.live_intervals_in_slot_span_of(&selected) {
                    crate::instrumentation::record_deterministic_work(1);
                    let low = (i128::from(low) + i128::from(delta.constant))
                        .clamp(0, i128::from(count)) as u32;
                    let high = (i128::from(high) + i128::from(delta.constant))
                        .clamp(0, i128::from(count)) as u32;
                    holes.insert_range(low, high);
                }
            } else {
                // Different spellings or strides require exact slot checks.
                // Enumerate only the selected overlap, not the rest of the
                // held run; this fallback costs the selected slots.
                for index in run
                    .live_intervals_in_slot_span_of(&selected)
                    .flat_map(|(low, high)| low..high)
                {
                    crate::instrumentation::record_deterministic_work(1);
                    if let Some(slot) = probe.slot_index(&run.slot_pointer(index)) {
                        holes.insert(slot);
                    }
                }
            }
        }
        if holes.count() >= u64::from(count) {
            return self;
        }
        let run = probe.with_holes(holes);
        let derivation_base = intern_derivation_base(&mut self);
        std::sync::Arc::make_mut(&mut self.cells).add_run(run.clone());
        record_c_memory_derivation(
            &mut self,
            CMemoryDerivation::CellsSeeded {
                base: derivation_base,
                run: std::sync::Arc::new(run),
            },
        );
        self
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
    /// [`Self::with_seeded_cells`], a snapshot with typed union views or a
    /// base that may lie in a live allocation.
    pub(crate) fn with_named_cell_run(
        self,
        base: Pointer,
        element_width: u32,
        element_type: CType,
        first: u32,
        count: u32,
        source: SharedCMemory,
    ) -> Result<Self, Self> {
        if first >= count {
            return Ok(self);
        }
        if base.block.starts_with("local:")
            || matches!(base.block, PointerBlock::Heap(_))
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

    /// [`Self::materialize_named_cell`] of every element of a symbolic
    /// static-storage array of `count` elements of `element_type` at `base`,
    /// each holding its symbolic entry value in `source`
    /// ([`crate::kernel::eval::symbolic_storage_cell_value`]), as one
    /// [`CellRun`] at a cost that does not depend on `count`; see
    /// [`Self::with_named_cell_run`], whose refusals this shares. The
    /// caller has declared the elements' access widths.
    pub(crate) fn with_symbolic_storage_run(
        self,
        base: Pointer,
        element_type: CType,
        count: u32,
        source: SharedCMemory,
    ) -> Result<Self, Self> {
        if count == 0 {
            return Ok(self);
        }
        if base.block.starts_with("local:")
            || matches!(base.block, PointerBlock::Heap(_))
            || !self.run_can_stand_for_cells_at(&base)
        {
            return Err(self);
        }
        Ok(self.with_run_of_cells(
            base,
            element_type.byte_width(),
            element_type,
            0,
            count,
            source,
            RunValueMode::SymbolicStorage,
        ))
    }

    /// [`Self::with_symbolic_storage_run`] for an array of `count` structs
    /// `stride` bytes apart at `base`, whose scalar fields are `fields` (each
    /// one's offset within the struct and type): one [`CellRun`] per field,
    /// stepping by `stride`, at a cost of the fields and the block's existing
    /// cells rather than the struct count. A field element that already
    /// holds a cell keeps it, as [`Self::materialize_named_cell`] would. The
    /// refusals are [`Self::with_symbolic_storage_run`]'s, and a block that
    /// already holds a run is refused too, so no two runs' slots meet.
    pub(crate) fn with_symbolic_storage_runs(
        mut self,
        base: &Pointer,
        stride: u32,
        count: u32,
        fields: &[(u32, CType)],
        source: SharedCMemory,
    ) -> Result<Self, Self> {
        if base.block.starts_with("local:")
            || matches!(base.block, PointerBlock::Heap(_))
            || !self.run_can_stand_for_cells_at(base)
            || self.cells.runs_in_block(&base.block).next().is_some()
        {
            return Err(self);
        }
        let existing = AliasCandidates::only_block(&base.block)
            .entries(self.cells.concrete())
            .map(|(pointer, _)| pointer.clone())
            .collect::<Vec<_>>();
        for (offset, element_type) in fields {
            crate::instrumentation::record_deterministic_work(1 + existing.len());
            let probe = CellRun::new_with_mode(
                base.offset_by_bytes(*offset),
                stride,
                *element_type,
                count,
                source.clone(),
                RunValueMode::SymbolicStorage,
                IndexIntervals::default(),
            );
            let mut holes = IndexIntervals::default();
            for pointer in &existing {
                if let Some(index) = probe.slot_index(pointer) {
                    holes.insert(index);
                }
            }
            if holes.count() >= u64::from(count) {
                continue;
            }
            let run = probe.with_holes(holes);
            let derivation_base = intern_derivation_base(&mut self);
            std::sync::Arc::make_mut(&mut self.cells).add_run(run.clone());
            record_c_memory_derivation(
                &mut self,
                CMemoryDerivation::CellsSeeded {
                    base: derivation_base,
                    run: std::sync::Arc::new(run),
                },
            );
        }
        Ok(self)
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
    /// does not), and, as for [`Self::with_seeded_cells`], a snapshot with
    /// typed union views or a base that may lie in a live allocation.
    pub(crate) fn with_constant_run(
        self,
        base: Pointer,
        element_type: CType,
        count: u32,
        value: CValue,
    ) -> Result<Self, Self> {
        if count == 0 {
            return Ok(self);
        }
        if base.block.starts_with("local:")
            || matches!(base.block, PointerBlock::Heap(_))
            || value.c_type() != element_type
            || !self.run_can_stand_for_cells_at(&base)
            || AliasCandidates::only_block(&base.block)
                .entries(self.cells.concrete())
                .next()
                .is_some()
            || self.cells.runs_in_block(&base.block).next().is_some()
        {
            return Err(self);
        }
        let source = crate::kernel::intern_c_memory(CMemory::new());
        Ok(self.with_run_of_cells(
            base,
            element_type.byte_width(),
            element_type,
            0,
            count,
            source,
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
        mut self,
        base: &Pointer,
        runs: &[CConstantRun],
    ) -> Result<Self, Self> {
        if matches!(base.block, PointerBlock::Heap(_))
            || !self.run_can_stand_for_cells_at(base)
            || AliasCandidates::only_block(&base.block)
                .entries(self.cells.concrete())
                .next()
                .is_some()
            || self.cells.runs_in_block(&base.block).next().is_some()
            || runs.iter().any(|run| {
                run.stride == 0 || (run.count > 1 && run.value.byte_width() > run.stride)
            })
        {
            return Err(self);
        }
        let source = crate::kernel::intern_c_memory(CMemory::new());
        for run in runs.iter().filter(|run| run.count > 0) {
            crate::instrumentation::record_deterministic_work(1);
            let run = CellRun::new_with_mode(
                base.offset_by_bytes(run.offset),
                run.stride,
                run.value.c_type(),
                run.count,
                source.clone(),
                RunValueMode::Constant(run.value.clone()),
                IndexIntervals::default(),
            );
            let derivation_base = intern_derivation_base(&mut self);
            std::sync::Arc::make_mut(&mut self.cells).add_run(run.clone());
            record_c_memory_derivation(
                &mut self,
                CMemoryDerivation::CellsSeeded {
                    base: derivation_base,
                    run: std::sync::Arc::new(run),
                },
            );
        }
        Ok(self)
    }

    /// Checked compact initialization of one fresh automatic scalar array.
    /// The caller has separately checked read/write authority and coercion.
    pub(in crate::kernel) fn initialize_scalar_array(
        self,
        base: &Pointer,
        element_type: CType,
        count: u32,
        value: CValue,
        copy: bool,
    ) -> Result<Self, CRuntimeError> {
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

    pub(in crate::kernel) fn write_scalar_array_region(
        mut self,
        base: &Pointer,
        element_type: CType,
        count: u32,
        value: CValue,
        copy: bool,
        fresh: bool,
        assumptions: &PureFactContext,
    ) -> Result<Self, CRuntimeError> {
        let bytes = count
            .checked_mul(element_type.byte_width())
            .filter(|bytes| *bytes <= i32::MAX as u32)
            .ok_or(CRuntimeError::TypeMismatch)?;
        let snapshot_copy = copy
            && matches!(&value, CValue::Pointer(source) if
            !source.pointer().block.starts_with("local:")
            || self.cells.runs_in_block(&source.pointer().block)
                .any(|run| !matches!(run.value_mode(), RunValueMode::Constant(_))));
        if !base.block.starts_with("local:") || snapshot_copy {
            return self.write_scalar_array_snapshot(
                base,
                element_type,
                count,
                value,
                copy,
                fresh,
                assumptions,
            );
        }
        let valid_region = |pointer: &Pointer| {
            pointer.block.starts_with("local:")
                && pointer.offset.as_const().is_some_and(|offset| {
                    offset >= 0
                        && offset % i64::from(element_type.byte_width()) == 0
                        && self
                            .block_size(&pointer.block)
                            .and_then(Bitvector32Term::as_const)
                            .is_some_and(|size| {
                                offset
                                    .checked_add(i64::from(bytes))
                                    .is_some_and(|end| end <= i64::from(size))
                            })
                })
        };
        if !matches!(element_type, CType::Int32 | CType::UInt8 | CType::UInt32)
            || !valid_region(base)
            || !self.run_can_stand_for_cells_at(base)
            || (fresh
                && (base.offset != PointerOffsetTerm::Constant(0)
                    || self
                        .block_size(&base.block)
                        .and_then(Bitvector32Term::as_const)
                        != Some(bytes)
                    || AliasCandidates::only_block(&base.block)
                        .entries(self.cells.concrete())
                        .next()
                        .is_some()
                    || self.cells.runs_in_block(&base.block).next().is_some()))
        {
            return Err(CRuntimeError::FunctionContract(
                "scalar-array write requires a valid aligned local region; fresh initialization requires complete empty storage".into(),
            ));
        }
        // Capture represented values before changing the destination, including
        // overlapping copies. Constant spans stay compact; explicit lanes retain
        // their immutable values rather than referring back to mutable storage.
        let mut spans = Vec::new();
        let mut cells = Vec::new();
        if copy {
            let CValue::Pointer(pointer) = &value else {
                return Err(CRuntimeError::TypeMismatch);
            };
            let pointer = pointer.pointer();
            if !valid_region(pointer)
                || !self.run_can_stand_for_cells_at(pointer)
                || (bytes != 0 && !self.has_initialized_bytes_under(pointer, bytes, assumptions))
                || (fresh
                    && (pointer.offset != PointerOffsetTerm::Constant(0)
                        || self
                            .block_size(&pointer.block)
                            .and_then(Bitvector32Term::as_const)
                            != Some(bytes)))
            {
                return Err(CRuntimeError::FunctionContract(
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
                CRuntimeError::FunctionContract(format!(
                    "scalar-array copy requires complete represented scalar values: {reason}"
                ))
            };
            for run in self.cells.runs_in_block(&pointer.block) {
                crate::instrumentation::record_deterministic_work(1);
                let Some(run_start) = run.base().offset.as_const() else {
                    return Err(invalid("symbolic run address"));
                };
                let run_end = i64::from(run.count())
                    .checked_mul(i64::from(run.element_width()))
                    .and_then(|bytes| run_start.checked_add(bytes))
                    .ok_or_else(|| invalid("run byte extent overflow"))?;
                if run_end <= start || end <= run_start {
                    continue;
                }
                let RunValueMode::Constant(value) = run.value_mode() else {
                    return Err(invalid("unsupported run values"));
                };
                if run.element_type() != element_type
                    || value.c_type() != element_type
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
            let at = |offset| Pointer {
                block: pointer.block.clone(),
                offset: PointerOffsetTerm::Constant(offset),
            };
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
                .is_some_and(|(at, _)| at.block == pointer.block)
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
                    || value.c_type() != element_type
                {
                    return Err(invalid(&format!(
                        "cell at byte {offset} with type {:?} does not fit {element_type:?} region {start}..{end}",
                        value.c_type()
                    )));
                }
                let index = ((offset - start) / width) as u32;
                covered.insert(index);
                cells.push((index, value.clone()));
            }
            if covered != IndexIntervals::full(count) {
                // A checked call may forget cached values of initialized
                // automatic storage. Copy the current snapshot's unknown
                // lanes just as for external initialized storage, retaining
                // the represented lanes and the checks above.
                return self.write_scalar_array_snapshot(
                    base,
                    element_type,
                    count,
                    value,
                    copy,
                    fresh,
                    assumptions,
                );
            }
        } else {
            if value.c_type() != element_type {
                return Err(CRuntimeError::TypeMismatch);
            }
            spans.push((0, count, value));
        }
        if count == 0 {
            return Ok(self);
        }
        if !fresh {
            self = self.without_possible_aliasing_cells(base, bytes, assumptions);
        }
        let target_at = |index| Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::Constant(
                base.offset.as_const().unwrap()
                    + i64::from(index) * i64::from(element_type.byte_width()),
            ),
        };
        for (first, length, value) in spans {
            let run = CellRun::new_with_mode(
                target_at(first),
                element_type.byte_width(),
                element_type,
                length,
                crate::kernel::intern_c_memory(CMemory::new()),
                RunValueMode::Constant(value),
                IndexIntervals::default(),
            );
            let derivation_base = intern_derivation_base(&mut self);
            std::sync::Arc::make_mut(&mut self.cells).add_run(run.clone());
            record_c_memory_derivation(
                &mut self,
                CMemoryDerivation::CellsSeeded {
                    base: derivation_base,
                    run: std::sync::Arc::new(run),
                },
            );
        }
        for (index, value) in cells {
            self = self.store_with_context(target_at(index), value, assumptions);
        }
        Ok(self.with_initialized_object(base, bytes))
    }

    // Authority is checked by the statement executor. External argument
    // storage follows ordinary typed-load semantics: unknown initialized
    // bytes remain symbolic. Known automatic storage must be initialized.
    pub(in crate::kernel) fn write_scalar_array_snapshot(
        mut self,
        base: &Pointer,
        element: CType,
        count: u32,
        value: CValue,
        copy: bool,
        fresh: bool,
        assumptions: &PureFactContext,
    ) -> Result<Self, CRuntimeError> {
        let bytes = count
            .checked_mul(element.byte_width())
            .filter(|bytes| *bytes <= i32::MAX as u32)
            .ok_or(CRuntimeError::TypeMismatch)?;
        if !matches!(element, CType::Int32 | CType::UInt8 | CType::UInt32) {
            return Err(CRuntimeError::TypeMismatch);
        }
        if count == 0 {
            if (copy && !matches!(value, CValue::Pointer(_)))
                || (!copy && value.c_type() != element)
            {
                return Err(CRuntimeError::TypeMismatch);
            }
            return Ok(self);
        }
        let valid = |pointer: &Pointer| {
            let (stem, constant) = offset_stem_and_constant(&pointer.offset);
            let width = i64::from(element.byte_width());
            let aligned = constant % width == 0
                && match stem {
                    None => true,
                    Some(PointerOffsetTerm::Int32Scaled { byte_width, .. }) => {
                        byte_width % width == 0
                    }
                    _ => false,
                };
            pointer != &Pointer::null()
                && constant.checked_add(i64::from(bytes)).is_some()
                && aligned
                && self.run_can_stand_for_cells_at(pointer)
                && if self.has_block(&pointer.block) {
                    self.access_in_bounds(pointer, bytes)
                } else {
                    matches!(
                        pointer.block,
                        PointerBlock::ExternalArgument | PointerBlock::ExternalObject(_)
                    )
                }
        };
        if !valid(base)
            || (fresh
                && (!base.block.starts_with("local:")
                    || base.offset != PointerOffsetTerm::Constant(0)
                    || self
                        .block_size(&base.block)
                        .and_then(Bitvector32Term::as_const)
                        != Some(bytes)
                    || self.cells.runs_in_block(&base.block).next().is_some()
                    || AliasCandidates::only_block(&base.block)
                        .entries(self.cells.concrete())
                        .next()
                        .is_some()))
        {
            return Err(CRuntimeError::FunctionContract("scalar-array snapshot requires valid aligned storage; fresh storage must be complete and empty".into()));
        }
        let snapshot = crate::kernel::intern_c_memory(self.clone());
        let mut captured_runs = Vec::new();
        let mut captured_cells = Vec::new();
        if copy {
            let CValue::Pointer(pointer) = value else {
                return Err(CRuntimeError::TypeMismatch);
            };
            let pointer = pointer.pointer();
            if !valid(pointer)
                || (pointer.block.starts_with("local:")
                    && !self.has_initialized_bytes_under(pointer, bytes, assumptions))
            {
                return Err(CRuntimeError::FunctionContract(
                    "scalar-array snapshot requires a valid initialized source region".into(),
                ));
            }
            let (stem, start) = offset_stem_and_constant(&pointer.offset);
            let width = i64::from(element.byte_width());
            let mut represented = IndexIntervals::default();
            for run in self.cells.runs_in_block(&pointer.block) {
                crate::instrumentation::record_deterministic_work(1);
                let (run_stem, run_start) = offset_stem_and_constant(&run.base().offset);
                if run_stem != stem {
                    continue;
                }
                let delta = run_start
                    .checked_sub(start)
                    .ok_or(CRuntimeError::TypeMismatch)?;
                let end = delta
                    .checked_add(i64::from(run.count()) * i64::from(run.element_width()))
                    .ok_or(CRuntimeError::TypeMismatch)?;
                if end <= 0 || delta >= i64::from(bytes) {
                    continue;
                }
                if run.element_type() != element
                    || run.element_width() != element.byte_width()
                    || delta % width != 0
                {
                    return Err(CRuntimeError::TypeMismatch);
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
                        RunValueMode::Load | RunValueMode::SymbolicStorage => RunValueMode::Copy {
                            source_base: run.slot_pointer(source_index),
                        },
                    };
                    captured_runs.push(CellRun::new_with_mode(
                        base.offset_by_bytes(first * element.byte_width()),
                        element.byte_width(),
                        element,
                        length,
                        run.source().clone(),
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
                    .ok_or(CRuntimeError::TypeMismatch)?;
                if delta + i64::from(value.byte_width()) <= 0 || delta >= i64::from(bytes) {
                    continue;
                }
                if delta < 0
                    || delta + width > i64::from(bytes)
                    || delta % width != 0
                    || value.c_type() != element
                {
                    return Err(CRuntimeError::TypeMismatch);
                }
                let index = (delta / width) as u32;
                represented.insert(index);
                captured_cells.push((
                    base.offset_by_bytes(index * element.byte_width()),
                    value.clone(),
                ));
            }
            if represented != IndexIntervals::full(count) {
                captured_runs.push(CellRun::new_with_mode(
                    base.clone(),
                    element.byte_width(),
                    element,
                    count,
                    snapshot,
                    RunValueMode::Copy {
                        source_base: pointer.clone(),
                    },
                    represented,
                ));
            }
        } else {
            if value.c_type() != element {
                return Err(CRuntimeError::TypeMismatch);
            }
            captured_runs.push(CellRun::new_with_mode(
                base.clone(),
                element.byte_width(),
                element,
                count,
                crate::kernel::intern_c_memory(CMemory::new()),
                RunValueMode::Constant(value),
                IndexIntervals::default(),
            ));
        }
        if !fresh {
            // Compact writes must not fall back to visiting every logical
            // slot of a possibly aliasing run. Require a whole-footprint
            // decision (including ownership separation), or refuse promptly.
            for run in self
                .cells
                .candidate_runs(&AliasCandidates::of_block(&base.block))
            {
                crate::instrumentation::record_deterministic_work(1);
                let (kept, _) =
                    crate::kernel::reasoning::memory_resolution::run_slots_kept_by_store(
                        run,
                        base,
                        bytes,
                        assumptions,
                    );
                if matches!(
                    kept,
                    crate::kernel::primitives::SlotSet::PerSlot
                        | crate::kernel::primitives::SlotSet::AskWithin(_, _)
                ) {
                    return Err(CRuntimeError::FunctionContract(
                        "scalar-array snapshot requires a compact decision for possibly aliasing storage".into()));
                }
            }
        }
        if !fresh {
            self = self.without_possible_aliasing_cells(base, bytes, assumptions);
        }
        for run in captured_runs {
            let derivation_base = intern_derivation_base(&mut self);
            std::sync::Arc::make_mut(&mut self.cells).add_run(run.clone());
            record_c_memory_derivation(
                &mut self,
                CMemoryDerivation::CellsSeeded {
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
    fn run_can_stand_for_cells_at(&self, base: &Pointer) -> bool {
        self.heap.uninitialized_objects.is_empty()
            && self.union_cells.is_empty()
            && !AliasCandidates::of_block(&base.block)
                .any_entry(&self.heap.live_allocations, |_, _| true)
    }

    /// The run of [`Self::with_seeded_cells`], its preconditions checked.
    fn with_run_of_cells(
        mut self,
        base: Pointer,
        element_width: u32,
        element_type: CType,
        first: u32,
        count: u32,
        source: SharedCMemory,
        mode: RunValueMode,
    ) -> Self {
        let mut holes = IndexIntervals::default();
        holes.insert_range(0, first);
        let probe = CellRun::new_with_mode(
            base.clone(),
            element_width,
            element_type,
            count,
            source.clone(),
            mode,
            IndexIntervals::default(),
        );
        // An element that already holds a cell keeps it: seeding skips it,
        // so it is a hole of the new run from the start. Only the cells of
        // the run's own block can be one of its slots.
        let own = AliasCandidates::only_block(&base.block);
        for (pointer, _) in own.entries(self.cells.concrete()) {
            if let Some(index) = probe.slot_index(pointer) {
                holes.insert(index);
            }
        }
        for run in self.cells.runs_in_block(&base.block) {
            if run.base() == &base && run.element_width() == element_width {
                // One spelling, one stride: the live slots of the older run
                // are the elements it has in common with this one.
                for (low, high) in run.holes().gaps(run.count()) {
                    holes.insert_range(low.min(count), high.min(count));
                }
                continue;
            }
            for index in run.live_indexes() {
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
        record_c_memory_derivation(
            &mut self,
            CMemoryDerivation::CellsSeeded {
                base: derivation_base,
                run: std::sync::Arc::new(run),
            },
        );
        self
    }

    pub fn store(self, pointer: Pointer, value: CValue) -> Self {
        self.store_with_context(pointer, value, &PureFactContext::new())
    }

    /// Cache the canonical value of an already existing cell for a resource
    /// projection. This is not a C write and cannot establish initialization.
    /// The conservative store edge keeps memory-DAG lookup connected without
    /// granting any new initialized-cell or allocation authority.
    pub(crate) fn materialize_named_cell(self, pointer: Pointer, value: CValue) -> Self {
        self.materialize_named_cell_under(pointer, value, &PureFactContext::new())
    }

    pub(crate) fn materialize_named_cell_under(
        mut self,
        pointer: Pointer,
        value: CValue,
        assumptions: &PureFactContext,
    ) -> Self {
        if self.cells.contains_key(&pointer) {
            return self;
        }
        if self.may_read_uninitialized_object_under(&pointer, value.byte_width(), assumptions)
            && !self.has_initialized_bytes_at(&pointer, value.byte_width())
        {
            return self;
        }
        // A logical name does not initialize an automatic object either.
        // A real local store has already materialized its cell above.
        if pointer.block.starts_with("local:") && self.has_block(&pointer.block) {
            return self;
        }
        // A named load must not turn fresh malloc storage into a value.  The
        // exact typed-cell mark is the authority that a prior C store
        // initialized this address; the lookup is local to its heap block.
        if matches!(pointer.block, PointerBlock::Heap(_)) {
            let base = Pointer {
                block: pointer.block.clone(),
                offset: PointerOffsetTerm::Constant(0),
            };
            if (self.heap.uninitialized_allocations.contains(&base)
                || self.heap.zeroed_allocations.contains(&base)
                || self.heap.zeroed_prefix_allocations.contains_key(&base))
                && !self.has_initialized_bytes_at(&pointer, value.byte_width())
            {
                return self;
            }
        }
        let base = intern_derivation_base(&mut self);
        std::sync::Arc::make_mut(&mut self.cells).insert(pointer.clone(), value.clone());
        record_c_memory_derivation(
            &mut self,
            CMemoryDerivation::Store {
                base,
                pointer,
                value,
            },
        );
        self
    }

    /// Retain a body-certified final pointer-cell equation. This does not
    /// initialize storage or grant allocation/access authority.
    pub(in crate::kernel) fn with_certified_pointer_cell(
        mut self,
        pointer: Pointer,
        value: CPointerValue,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        if value.designation().is_none()
            || !self.has_initialized_bytes_under(&pointer, value.c_type().byte_width(), assumptions)
        {
            return None;
        }
        let value = CValue::Pointer(value);
        let base = intern_derivation_base(&mut self);
        std::sync::Arc::make_mut(&mut self.cells).insert(pointer.clone(), value.clone());
        record_c_memory_derivation(
            &mut self,
            CMemoryDerivation::Store {
                base,
                pointer,
                value,
            },
        );
        Some(self)
    }

    /// Writes one cell. The transition's fact context is not recorded on the
    /// store edge: a later load of another cell of the same base crosses the
    /// edge only with distinctness evidence checked in the querying context.
    pub fn store_with_context(
        mut self,
        pointer: Pointer,
        value: CValue,
        context: &PureFactContext,
    ) -> Self {
        // Most scalar stores have no union views to displace. When one is
        // present, forget views at every possibly overlapping spelling before
        // recording the new scalar cell.
        if !self.union_cells.is_empty() {
            self = self.without_possible_aliasing_cells(&pointer, value.byte_width(), context);
        }
        let base = intern_derivation_base(&mut self);
        std::sync::Arc::make_mut(&mut self.cells).insert(pointer.clone(), value.clone());
        if (self.is_live_heap_address(&pointer, context)
            || !self.heap.uninitialized_objects.is_empty())
            && !self.heap.initialized.covers(&pointer, value.byte_width())
        {
            std::sync::Arc::make_mut(&mut self.heap)
                .initialized
                .record(&pointer, value.byte_width());
        }
        // Skipped when empty so an ordinary store neither visits nor
        // reallocates the shared overlay map.
        if !self.union_cells.is_empty() {
            self.remove_union_views_at(&pointer);
        }
        record_c_memory_derivation(
            &mut self,
            CMemoryDerivation::Store {
                base,
                pointer,
                value,
            },
        );
        self
    }

    pub fn load(&self, pointer: &Pointer) -> CExpressionOutcome {
        match self.cells.get(pointer) {
            Some(value) => CExpressionOutcome::Value(value),
            None => CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory),
        }
    }

    /// The pointers at which the two snapshots' cells or typed union views
    /// differ, ascending. A pointer differs exactly when some entry keyed by
    /// it is in one map's diff, so this walks only the paths the snapshots
    /// do not share.
    pub fn differing_cell_pointers(&self, other: &Self) -> Vec<Pointer> {
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
        pointer: &Pointer,
        bytes: u32,
    ) -> Vec<Pointer> {
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

    pub(in crate::kernel) fn known_value(&self, pointer: &Pointer) -> Option<CValue> {
        self.cells.get(pointer)
    }

    pub(in crate::kernel) fn has_known_cell_at(&self, pointer: &Pointer) -> bool {
        self.cells.contains_key(pointer) || self.has_union_overlay_at(pointer)
    }

    /// The typed union views recorded at exactly `pointer`: one key range,
    /// since `(Pointer, CType)` keys order by pointer first.
    fn union_views_at<'a>(
        &'a self,
        pointer: &'a Pointer,
    ) -> impl Iterator<Item = (&'a (Pointer, CType), &'a CValue)> + 'a {
        self.union_cells
            .range::<_, (Pointer, CType)>((pointer.clone(), CType::Void)..)
            .take_while(move |((cell_pointer, _), _)| cell_pointer == pointer)
    }

    /// Drops every typed union view at exactly `pointer`.
    fn remove_union_views_at(&mut self, pointer: &Pointer) {
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
    /// block holding it; a symbolic offset by its indexed offset-family run.
    pub(in crate::kernel) fn has_initialized_bytes_at(
        &self,
        pointer: &Pointer,
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
    fn written_interval(&self, block: &PointerBlock, start: i64, end: i64) -> bool {
        let at = |offset: i64| Pointer {
            block: block.clone(),
            offset: PointerOffsetTerm::Constant(offset),
        };
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
        pointer: &Pointer,
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
        pointer: &Pointer,
        byte_width: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        if self.has_initialized_bytes_at(pointer, byte_width) {
            return true;
        }
        // An exact cached store is initialization evidence at symbolic addresses
        // too. Keep the query local to this cell; unrelated addresses and bytes
        // beyond the stored value still require their own evidence.
        if self
            .cells
            .get(pointer)
            .is_some_and(|value| value.byte_width() >= byte_width)
        {
            return true;
        }
        if let Some(offset) = pointer.offset.as_const() {
            return self.written_interval(&pointer.block, offset, offset + i64::from(byte_width));
        }
        let (atoms, shift) =
            crate::kernel::reasoning::memory_resolution::offset_atoms_and_constant(&pointer.offset);
        let [
            PointerOffsetTerm::Int32Scaled {
                value,
                byte_width: scale,
            },
        ] = atoms.as_slice()
        else {
            return false;
        };
        if *scale <= 0 {
            return false;
        }
        let Some((low, high)) = assumptions.signed_interval(value) else {
            return false;
        };
        let (Some(start), Some(end)) = (
            low.checked_mul(*scale)
                .and_then(|bytes| bytes.checked_add(shift)),
            high.checked_mul(*scale)
                .and_then(|bytes| bytes.checked_add(shift))
                .and_then(|bytes| bytes.checked_add(i64::from(byte_width))),
        ) else {
            return false;
        };
        start < end && self.written_interval(&pointer.block, start, end)
    }

    /// Whether any typed union overlay is recorded at exactly this pointer.
    ///
    /// A union overlay is the authoritative view for an exact typed load, so a
    /// reader that wants to treat the raw cell as the pointer's content has to
    /// know that no overlay outranks it. [`Self::store_with_context`] and
    /// [`Self::store_union`] keep the two disjoint at every pointer, so this
    /// answers `false` wherever [`Self::known_value`] answers `Some`; it is
    /// asked anyway where the consequence of the two ever coexisting would be
    /// a wrong value rather than a lost one.
    pub(in crate::kernel) fn has_union_overlay_at(&self, pointer: &Pointer) -> bool {
        self.union_views_at(pointer).next().is_some()
    }

    pub(in crate::kernel) fn known_union_value(
        &self,
        pointer: &Pointer,
        value_type: CType,
    ) -> Option<CValue> {
        self.union_cells
            .get(&(pointer.clone(), value_type))
            .cloned()
    }

    #[cfg(test)]
    pub(in crate::kernel) fn store_union(
        self,
        pointer: Pointer,
        value_type: CType,
        value: CValue,
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
        written_pointer: Pointer,
        written_bytes: u32,
        views: Vec<(Pointer, CType, CValue)>,
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
                .insert((pointer.clone(), value_type), value);
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
                CValue::pointer(written_pointer.clone()),
                CValue::Int32(written_bytes.into()),
            ],
        );
        memory
    }

    /// Drops every cell a field of `c_type` at `offset_bytes` from `base`
    /// could occupy.
    ///
    /// Used where a copy cannot carry a field's value: leaving the
    /// destination's own cells would read back as its previous contents,
    /// which no execution of the copy produces.
    pub(in crate::kernel) fn without_field_cells(
        &self,
        base: &Pointer,
        offset_bytes: u32,
        c_type: CType,
    ) -> Self {
        let diagnostic_base = self.clone();
        let Some(field_start) = base
            .offset
            .as_const()
            .map(|start| start + i64::from(offset_bytes))
        else {
            return self.clone();
        };
        let field_end = field_start + i64::from(c_type.byte_width());
        let mut memory = self.clone();
        let source = intern_c_memory_ref(&memory);
        let overlaps = |pointer: &Pointer| {
            pointer.block == base.block
                && pointer
                    .offset
                    .as_const()
                    .is_some_and(|offset| offset >= field_start && offset < field_end)
        };
        // `overlaps` holds only in the base's own block.
        let own = AliasCandidates::only_block(&base.block);
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
        memory.forget_zero_readings_under(std::iter::once(&base.block));
        // The copy wrote the field with no value it can name, from a source
        // whose field it could not check, so its bytes are not known
        // initialized either.
        memory.forget_initialized_bytes(
            &Pointer {
                block: base.block.clone(),
                offset: PointerOffsetTerm::Constant(field_start),
            },
            c_type.byte_width(),
        );
        // Nothing restores these cells — the copy could not carry the field —
        // so the result knows strictly less than its source and must not be
        // able to re-intern as a state that never knew it. See
        // [`CMemory::mark_forgotten_from`].
        if memory.cells.len() != self.cells.len()
            || memory.union_cells.len() != self.union_cells.len()
        {
            memory.mark_forgotten_from(&source);
        }
        memory.record_diagnostic_transform(
            "forget copied field contents",
            vec![diagnostic_base],
            vec![
                CValue::pointer(base.clone()),
                CValue::Int32(offset_bytes.into()),
                CValue::Int32(c_type.byte_width().into()),
            ],
        );
        memory
    }

    pub(in crate::kernel) fn without_cell(&self, pointer: &Pointer) -> Self {
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
            vec![CValue::pointer(pointer.clone())],
        );
        memory
    }

    /// Records the bytes of cells whose cached values an operation dropped
    /// as initialized: forgetting a value does not end its storage lifetime
    /// or undo initialization. This also covers symbolic contract inputs whose
    /// complete typed cells were admitted at entry. Costs the dropped cells.
    fn record_dropped_initialized_cells(&mut self, dropped: &[(Pointer, u32)]) {
        let mut record = self.heap.initialized.clone();
        let mut changed = false;
        for (pointer, width) in dropped {
            changed |= record.record(pointer, *width);
        }
        if changed {
            std::sync::Arc::make_mut(&mut self.heap).initialized = record;
        }
    }

    /// The one way a memory transition drops cached contents.
    ///
    /// A snapshot records what an address holds in more than one place: a
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
    /// reading, and stays recorded initialized (forgetting a cached value
    /// does not undo initialization). A new representation of cached bytes
    /// belongs in this function, so no transition can miss it.
    ///
    /// The slots `run_rule` drops as a whole run are recorded initialized
    /// by [`Self::record_dropped_initialized_run_slots`],
    /// whatever `fate` would say of them: a dropped slot was written, and a
    /// caller that retires the storage forgets its record afterwards. A run
    /// carries no zero reading to lose: it is never seeded where a live
    /// allocation may lie ([`Self::with_seeded_cells`] and its siblings
    /// refuse one).
    ///
    /// The work is the candidates `scope` admits, which every caller already
    /// pays for its cells; the union views are asked only when the snapshot
    /// holds some, and the zero readings only when it holds some. Returns
    /// whether any value was [`CachedValueFate::Forgotten`].
    pub(super) fn forget_cached_values(
        &mut self,
        scope: ForgetScope<'_>,
        mut fate: impl FnMut(&Pointer, CachedValue<'_>) -> CachedValueFate,
        run_rule: impl FnMut(&CellRun) -> (SlotSet, crate::kernel::primitives::RuleAnswer),
    ) -> bool {
        let mut forgotten_cells = Vec::new();
        let dropped_run_slots;
        {
            let mut keep_cell =
                |pointer: &Pointer, value: &CValue| match fate(pointer, CachedValue::Cell(value)) {
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
                } => cells.retain_selected_concrete_by(
                    selected,
                    candidates,
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
            let mut keep_view = |(pointer, c_type): &(Pointer, CType), value: &CValue| match fate(
                pointer,
                CachedValue::UnionView(*c_type, value),
            ) {
                CachedValueFate::Kept => true,
                CachedValueFate::Overwritten | CachedValueFate::Retired => false,
                CachedValueFate::Forgotten => {
                    push_dropped_initialized(
                        &mut forgotten_cells,
                        (pointer.clone(), c_type.byte_width()),
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
        self.record_dropped_initialized_cells(&forgotten_cells);
        // A run's slots are cells too, dropped by `run_rule` as a whole run
        // without `fate` being asked; automatic ones stay initialized.
        self.record_dropped_initialized_run_slots(&dropped_run_slots);
        self.forget_zero_readings_under(forgotten_cells.iter().map(|(pointer, _)| &pointer.block));
        !forgotten_cells.is_empty()
    }

    /// Drops the zero reading of every allocation that may hold a byte of
    /// `blocks`: every one in a block not proven distinct from one of them.
    /// A zero reading answers for the bytes no cached value covers, so once a
    /// cached value under it is forgotten, the reading would answer zero for
    /// bytes that held something else. The allocation goes as a whole, as a
    /// call's write set takes it ([`Self::forget_zeroed_allocations_written_by`]).
    /// Costs nothing when no allocation reads as zero, and otherwise the
    /// distinct blocks plus the readings dropped.
    fn forget_zero_readings_under<'a>(&mut self, blocks: impl Iterator<Item = &'a PointerBlock>) {
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
    /// slots are one run of bytes, including at symbolic offsets; only slots
    /// strided apart are recorded one by one, each as a dropped cell.
    fn record_dropped_initialized_run_slots(&mut self, dropped: &[DroppedRunSlots]) {
        if dropped.is_empty() {
            return;
        }
        let mut record = self.heap.initialized.clone();
        let mut changed = false;
        for DroppedRunSlots { run, elements } in dropped {
            let width = run.value_width();
            for (low, high) in elements.intervals() {
                if low >= high {
                    continue;
                }
                let first = run.slot_pointer(low);
                // Adjacent slots remain one initialized interval even when
                // the run's base is a symbolic parameter address.
                if run.element_width() == width
                    && let Some(bytes) = (high - low).checked_mul(width)
                {
                    changed |= record.record(&first, bytes);
                    continue;
                }
                let span = first.offset.as_const().zip(
                    run.slot_pointer(high - 1)
                        .offset
                        .as_const()
                        .map(|last| last + i64::from(width)),
                );
                if let Some((start, end)) = span {
                    if record.covers_interval(&first.block, start, end) {
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
    pub(in crate::kernel) fn with_initialized_object(
        mut self,
        pointer: &Pointer,
        bytes: u32,
    ) -> Self {
        if !self.heap.initialized.covers(pointer, bytes) {
            let base = intern_derivation_base(&mut self);
            std::sync::Arc::make_mut(&mut self.heap)
                .initialized
                .record(pointer, bytes);
            record_c_memory_derivation(
                &mut self,
                CMemoryDerivation::ObjectInitializationRecorded {
                    base,
                    pointer: pointer.clone(),
                    bytes,
                },
            );
        }
        self
    }

    /// Forgets the initialization of the `byte_width` bytes at `pointer`
    /// (see [`InitializedBytes::forget`]), leaving the heap shared when the
    /// record holds none of them.
    fn forget_initialized_bytes(&mut self, pointer: &Pointer, byte_width: u32) {
        let mut record = self.heap.initialized.clone();
        if record.forget(pointer, byte_width) {
            std::sync::Arc::make_mut(&mut self.heap).initialized = record;
        }
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
    /// [`access_byte_overlap`], exactly as `step_effect::cell_effect` and the
    /// snapshot comparisons conjoin it: the ladder decides whether the
    /// addresses differ, and the byte answer decides whether the gap it
    /// establishes clears both accesses. An unknown gap blocks it too — a
    /// ladder proving two addresses differ says nothing about bytes.
    ///
    /// The widths are exact on both sides here, which is why this site can
    /// ask at all: the store's is its own `bytes`, and the cell's is the
    /// width of the value it holds, standing in the widest scalar where it
    /// holds none. Over-stating a width can only shrink the separated set,
    /// and a cell that stops being shown separate is dropped, which loses
    /// knowledge rather than keeping a stale value.
    pub(in crate::kernel) fn without_possible_aliasing_cells(
        &self,
        pointer: &Pointer,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> Self {
        let normalized_pointer = Pointer {
            block: pointer.block.clone(),
            offset: normalize_exact_memory_loads_in_pointer_offset(&pointer.offset, assumptions),
        };
        // Computed once for the whole scan; the cells it is compared against
        // are the same-block ones, so the write's own atoms never change.
        let written = crate::kernel::reasoning::StoreByteInterval::of(&normalized_pointer, bytes);
        let mut memory = self.clone();
        let base = Some(intern_derivation_base(&mut memory));
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
        let candidates = AliasCandidates::of_block(&normalized_pointer.block);
        // Ownership first. A cell that a resource composition owns through a
        // different member than the written bytes is kept by the partition
        // law, whichever rung below would have found that out; asking it
        // first, through the composition's base index, spares such cells the
        // pure-fact distinctness ladder, whose failing searches cost work in
        // every separation fact of the block. Cells ownership does not place
        // go down the ladder unchanged.
        let owned_footprint = assumptions.owned_store_footprint(&normalized_pointer, bytes);
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
        let cell_fate = |cell_pointer: &Pointer, cell_value: &CValue| {
            let normalized_cell_pointer = Pointer {
                block: cell_pointer.block.clone(),
                offset: normalize_exact_memory_loads_in_pointer_offset(
                    &cell_pointer.offset,
                    assumptions,
                ),
            };
            if normalized_cell_pointer.block == normalized_pointer.block
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
            if assumptions.access_owned_apart_from_store(
                &owned_footprint,
                &normalized_pointer,
                &normalized_cell_pointer,
                crate::kernel::reasoning::cell_access_byte_width(cell_value),
            ) {
                return CachedValueFate::Kept;
            }
            let address_inequality_separates_bytes = crate::kernel::reasoning::access_byte_overlap(
                &normalized_cell_pointer,
                crate::kernel::reasoning::cell_access_byte_width(cell_value),
                &normalized_pointer,
                bytes,
                assumptions,
            )
                == crate::kernel::reasoning::AccessByteOverlap::Separate;
            let kept = address_inequality_separates_bytes
                && pointers_proven_distinct_for_memory_resolution(
                    &normalized_cell_pointer,
                    &normalized_pointer,
                    assumptions,
                )
                // A range partition keeps the cached value only when both
                // complete accesses fit their separated ranges. Starting
                // address membership alone cannot preserve its later bytes.
                || crate::kernel::memory_provenance::typed_store_separated_ranges_evidence(
                    &normalized_pointer,
                    bytes,
                    &normalized_cell_pointer,
                    crate::kernel::reasoning::cell_access_byte_width(cell_value),
                    assumptions,
                )
                .is_some()
                // Last: a separating composition owns the written address and
                // this cell's address through two different members, so the
                // partition invariant keeps the cell. Kept here beside the
                // range scan above, for the same reason: once the store has
                // dropped a cell, the two snapshots differ *at the read's own
                // address*, and no later framing route can recover it — the
                // question is only decidable while the cell is still there.
                || crate::kernel::memory_provenance::owned_composition_store_separated_evidence(
                    &normalized_pointer,
                    bytes,
                    &normalized_cell_pointer,
                    crate::kernel::reasoning::cell_access_byte_width(cell_value),
                    assumptions,
                )
                .is_some();
            if kept {
                CachedValueFate::Kept
            } else {
                CachedValueFate::Forgotten
            }
        };
        let view_fate = |cell_pointer: &Pointer, cell_type: CType| {
            let normalized_cell_pointer = Pointer {
                block: cell_pointer.block.clone(),
                offset: normalize_exact_memory_loads_in_pointer_offset(
                    &cell_pointer.offset,
                    assumptions,
                ),
            };
            if normalized_cell_pointer.block == normalized_pointer.block
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
                && pointers_proven_distinct_for_memory_resolution(
                    &normalized_cell_pointer,
                    &normalized_pointer,
                    assumptions,
                )
                || crate::kernel::memory_provenance::typed_store_separated_ranges_evidence(
                    &normalized_pointer,
                    bytes,
                    &normalized_cell_pointer,
                    cell_type.byte_width().max(1),
                    assumptions,
                )
                .is_some()
                || crate::kernel::memory_provenance::owned_composition_store_separated_evidence(
                    &normalized_pointer,
                    bytes,
                    &normalized_cell_pointer,
                    cell_type.byte_width().max(1),
                    assumptions,
                )
                .is_some();
            if kept {
                CachedValueFate::Kept
            } else {
                CachedValueFate::Forgotten
            }
        };
        #[cfg(debug_assertions)]
        if !gap_kept.is_empty() {
            crate::instrumentation::uncharged_debug_check(|| {
                crate::kernel::reasoning::store_gap::check_gap_kept_cells(
                    &memory.cells,
                    &gap_kept,
                    &normalized_pointer,
                    &mut |pointer: &Pointer, value: &CValue| {
                        cell_fate(pointer, value) == CachedValueFate::Kept
                    },
                );
            });
        }
        let ordered = memory.cells.ordered_store_candidates(
            &normalized_pointer,
            bytes,
            &candidates,
            assumptions,
        );
        let scope = match ordered.as_deref() {
            Some(selected) => ForgetScope::Ordered {
                candidates: &candidates,
                selected,
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
                CachedValue::UnionView(c_type, _) => view_fate(pointer, c_type),
            },
            run_rule,
        );
        let forgot_live_knowledge = forgot_values || run_forgot;
        // Forgetting nothing is not a transition: the memory is the same
        // snapshot, so a later load keeps resolving through it unchanged
        // instead of stopping at an edge that records no write.
        if memory.cells.len() == self.cells.len()
            && memory.union_cells.len() == self.union_cells.len()
        {
            return self.clone();
        }
        // A store never de-initializes: the heap marks of the cells it may
        // alias stay as they are, and `forget_cached_values` recorded the
        // automatic cells it forgot beside them.
        if let Some(base) = base {
            // The mark goes on before interning, because it is what the
            // result is interned *as*. Without it the emptied cell map can
            // re-intern as an older node — in the smallest case the function
            // entry state — and then this edge would run backwards, be
            // dropped, and leave the store that filled those cells off every
            // recorded history.
            if forgot_live_knowledge {
                memory.mark_forgotten_from(&base);
            }
            let base_id = base.arena_id();
            record_c_memory_derivation(&mut memory, CMemoryDerivation::CellsForgotten { base });
            // Check after producer recording: first interning also fixes the
            // read-congruence identity, so debug checks must not preempt it.
            debug_assert!(
                !forgot_live_knowledge || intern_c_memory_ref(&memory).arena_id() > base_id,
                "a forget that lost knowledge landed on an older snapshot"
            );
        }
        memory
    }

    /// Value-only parameters never own storage. Give their pseudo-slots a
    /// separate namespace so a caller's same-named local cannot supply a cell
    /// or be overwritten by a parameter assignment.
    pub(in crate::kernel) fn value_parameter_pointer(name: &str) -> Pointer {
        Pointer {
            block: format!("local:value-parameter:{name}").into(),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    pub(in crate::kernel) fn local_pointer(name: &str) -> Pointer {
        Pointer {
            block: format!("local:{name}").into(),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    pub(in crate::kernel) fn local_lifetime_pointer(lifetime: u64, name: &str) -> Pointer {
        Pointer {
            block: format!("local:lifetime:{lifetime}:{name}").into(),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    pub(crate) fn global_pointer(name: &str) -> Pointer {
        Self::global_pointer_named(name)
    }

    fn global_pointer_named(name: &str) -> Pointer {
        Pointer {
            block: format!("global:{name}").into(),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    pub(in crate::kernel) fn string_literal_pointer(
        function: &str,
        name: &str,
        bytes: &[u8],
    ) -> Pointer {
        Pointer {
            block: PointerBlock::StringLiteral {
                identity: format!("{function}:{name}"),
                bytes: bytes.to_vec(),
            },
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    pub(crate) fn static_pointer(function: &str, name: &str) -> Pointer {
        Pointer {
            block: format!("static:{function}:{name}").into(),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    pub(in crate::kernel) fn frame_local_pointer(frame: u64, name: &str) -> Pointer {
        Pointer {
            block: format!("local:frame:{frame}:{name}").into(),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    pub(crate) fn has_block(&self, block: &PointerBlock) -> bool {
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
                .any(|block| !block.starts_with("local:") && !block.starts_with("havoc:"))
    }

    pub(in crate::kernel) fn is_ended_local_block(&self, block: &PointerBlock) -> bool {
        self.forgotten.ended_local_blocks.contains(block)
    }

    /// Whether this memory and `other` are the same outside `blocks`: every
    /// block, cell, run and typed view on which they differ lies in one of
    /// `blocks`, and they agree on ended lifetimes, forget marks and the
    /// heap. Only the entries on which the two differ are visited.
    pub(in crate::kernel) fn differs_only_within(
        &self,
        other: &Self,
        blocks: &BTreeSet<PointerBlock>,
    ) -> bool {
        self.forgotten == other.forgotten
            && self.heap == other.heap
            && self
                .blocks
                .diff(&other.blocks)
                .all(|change| blocks.contains(change.key()))
            && self.cells.differs_only_within(&other.cells, blocks)
            && self
                .union_cells
                .diff(&other.union_cells)
                .all(|change| blocks.contains(&change.key().0.block))
    }

    /// The automatic objects whose lifetimes this memory records as ended.
    pub(in crate::kernel) fn ended_local_blocks(&self) -> impl Iterator<Item = &PointerBlock> {
        self.forgotten.ended_local_blocks.iter()
    }

    pub(in crate::kernel) fn is_ended_local_address(&self, pointer: &Pointer) -> bool {
        self.forgotten.ended_local_blocks.contains(&pointer.block)
    }

    /// Whether this memory has already given this block to an automatic
    /// object: one that is live, or one whose lifetime ended and whose
    /// tombstone still makes aliases to it invalid.
    ///
    /// Handing the same block to a second object would make the two one
    /// object at every site that reads `a.block == b.block`, so a declaration
    /// asks this before it mints.
    pub(in crate::kernel) fn local_block_is_occupied(&self, block: &PointerBlock) -> bool {
        self.blocks.contains_key(block) || self.forgotten.ended_local_blocks.contains(block)
    }

    /// A sufficient, search-free condition for transporting loadability of
    /// an exact range. Unlike value equality, this ignores writes, but never
    /// ignores changed block extents or allocation retirement metadata.
    pub(in crate::kernel) fn read_region_identity(&self, base: &Pointer) -> ReadRegionIdentity {
        crate::instrumentation::record_deterministic_work(1);
        ReadRegionIdentity {
            block_size: self.block_size(&base.block).cloned(),
            local_lifetime_ended: self.forgotten.ended_local_blocks.contains(&base.block),
            heap: self.heap.clone(),
        }
    }

    pub(in crate::kernel) fn has_call_memory_havoc(&self) -> bool {
        // Call-havoc markers are concrete blocks with this prefix. Bound the
        // B-tree query to that lexical interval so a load does not scan
        // unrelated memory blocks on the evaluator hot path.
        let first = PointerBlock::Concrete("call-havoc:".to_string());
        let end = PointerBlock::Concrete("call-havoc;".to_string());
        self.blocks.range(first..end).next().is_some()
    }

    pub(in crate::kernel) fn is_read_only_block(&self, block: &PointerBlock) -> bool {
        self.blocks.get(block).is_some_and(CBlock::is_read_only)
    }

    pub(in crate::kernel) fn block_size(&self, block: &PointerBlock) -> Option<&Bitvector32Term> {
        self.blocks.get(block).map(CBlock::size)
    }

    /// Whether some allocation this snapshot has already freed may contain
    /// `pointer`. Freed allocations are few, so this scans them directly.
    pub(in crate::kernel) fn freed_heap_allocation_may_contain(
        &self,
        pointer: &Pointer,
        assumptions: &PureFactContext,
    ) -> bool {
        self.heap
            .deallocated_allocations
            .keys()
            .any(|allocation| heap_allocation_may_contain_pointer(allocation, pointer, assumptions))
    }

    pub(in crate::kernel) fn is_loadable_concretely(
        &self,
        pointer: &Pointer,
        byte_width: u32,
    ) -> bool {
        // Read-only blocks are created only for fully materialized C string
        // literals. Their bytes are stable for the lifetime of the program,
        // so any in-bounds byte range is loadable even when it spans the
        // literal's individual uint8 cells.
        if self.is_read_only_block(&pointer.block) {
            return self.access_in_bounds(pointer, byte_width);
        }
        // The width alone decides, so a run slot's value is not named: a
        // question about a slot's presence costs the same whatever the
        // run's length, and whether the value was named earlier.
        self.cells.value_width_at(pointer) == Some(byte_width)
    }

    pub(in crate::kernel) fn string_literal_loadable_facts(&self) -> Vec<Proposition> {
        self.blocks
            .iter()
            .filter(|&(block, contents)| {
                contents.is_read_only() && matches!(block, PointerBlock::StringLiteral { .. })
            })
            .map(|(block, contents)| Proposition::CMemoryLoadable {
                memory: self.clone(),
                base: Pointer {
                    block: block.clone(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                bytes: contents.size().clone(),
                wide: false,
            })
            .collect()
    }

    pub(in crate::kernel) fn can_store_concretely(
        &self,
        pointer: &Pointer,
        value: &CValue,
    ) -> bool {
        !self.is_read_only_block(&pointer.block)
            && (self.cells.contains_key(pointer)
                || self.access_in_bounds(pointer, value.byte_width()))
    }

    pub(in crate::kernel) fn access_in_bounds(&self, pointer: &Pointer, byte_width: u32) -> bool {
        let Some(offset) = pointer.offset.as_const() else {
            return false;
        };
        let Ok(offset) = u32::try_from(offset) else {
            return false;
        };
        let Some(block) = self.blocks.get(&pointer.block) else {
            return false;
        };
        let Some(block_size) = block.size().as_const() else {
            return false;
        };
        offset
            .checked_add(byte_width)
            .is_some_and(|end| end <= block_size)
    }

    pub(in crate::kernel) fn symbolic_int32_load(&self, pointer: &Pointer) -> CValue {
        int32(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
            LoadKind::Bits32,
        ))
    }

    /// A signed byte read: the two's-complement conversion of the byte's
    /// one unsigned read ([`Bitvector32Term::memory_read`]).
    pub(in crate::kernel) fn symbolic_int8_load(&self, pointer: &Pointer) -> CValue {
        int8(Bitvector32Term::memory_read(
            crate::kernel::intern_c_memory(self.clone()),
            pointer.clone(),
            LoadKind::Int8,
        ))
    }

    pub(in crate::kernel) fn symbolic_int16_load(&self, pointer: &Pointer) -> CValue {
        int16(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
            LoadKind::Int16,
        ))
    }

    pub(in crate::kernel) fn symbolic_uint8_load(&self, pointer: &Pointer) -> CValue {
        uint8(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
            LoadKind::UInt8,
        ))
    }

    pub(in crate::kernel) fn symbolic_uint16_load(&self, pointer: &Pointer) -> CValue {
        uint16(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
            LoadKind::UInt16,
        ))
    }

    pub(in crate::kernel) fn symbolic_uint32_load(&self, pointer: &Pointer) -> CValue {
        uint32(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
            LoadKind::Bits32,
        ))
    }

    pub(in crate::kernel) fn symbolic_int64_load(&self, pointer: &Pointer) -> CValue {
        if let Some(CValue::PointerInteger(value)) = self.known_value(pointer)
            && value.c_type() == CType::Int64
        {
            return CValue::PointerInteger(value);
        }
        CValue::Int64(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
            LoadKind::Bits64,
        ))
    }

    pub(in crate::kernel) fn symbolic_uint64_load(&self, pointer: &Pointer) -> CValue {
        if let Some(CValue::PointerInteger(value)) = self.known_value(pointer)
            && value.c_type() == CType::UInt64
        {
            return CValue::PointerInteger(value);
        }
        CValue::UInt64(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
            LoadKind::Bits64,
        ))
    }

    pub(in crate::kernel) fn symbolic_wide_integer_load(
        &self,
        pointer: &Pointer,
        ty: MachineIntegerType,
    ) -> Option<CValue> {
        if ty.format().bits() != 128 {
            return None;
        }
        let load = Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
            LoadKind::of_type(ty.c_type())?,
        );
        Some(match ty {
            MachineIntegerType::Int128 => CValue::Int128(load),
            MachineIntegerType::UInt128 => CValue::UInt128(load),
            _ => return None,
        })
    }

    pub(in crate::kernel) fn symbolic_float32_load(&self, pointer: &Pointer) -> CValue {
        CValue::Float32(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
            LoadKind::Float32,
        ))
    }

    pub(in crate::kernel) fn symbolic_float64_load(&self, pointer: &Pointer) -> CValue {
        CValue::Float64(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
            LoadKind::Float64,
        ))
    }

    pub(in crate::kernel) fn symbolic_pointer_load(
        &self,
        pointer: &Pointer,
        pointee_byte_width: u32,
        value_type: CType,
    ) -> CValue {
        if let Some(CValue::Pointer(value)) = self.known_value(pointer)
            && value.designation().is_some()
        {
            return CValue::Pointer(value.with_type(value_type));
        }
        let snapshot = crate::kernel::intern_c_memory(self.clone());
        CValue::Pointer(CPointerValue::new(
            Pointer::loaded(
                pointer.block.clone(),
                Bitvector32Term::MemoryLoad(
                    snapshot.clone(),
                    Box::new(pointer.clone()),
                    LoadKind::Pointer,
                ),
                i64::from(pointee_byte_width),
            ),
            value_type,
        ))
    }
}

impl CState {
    pub(crate) fn typed_access_policy(&self) -> CTypedAccessPolicy {
        self.typed_access_policy
    }

    pub(crate) fn with_typed_access_policy(mut self, policy: CTypedAccessPolicy) -> Self {
        self.typed_access_policy = policy;
        self
    }

    /// Selects a call destination without allocating, initializing, or granting
    /// authority. Function entry validates it against the construction layout.
    pub fn with_aggregate_return_destination(
        mut self,
        pointer: Pointer,
        layout: CAggregateLayout,
    ) -> Self {
        self.aggregate_destination = Some(Arc::new(CAggregateDestination { pointer, layout }));
        self
    }

    /// O(1), fail-closed comparison of the non-memory part of a predicate's
    /// state argument. The caller has already checked exact interned memory
    /// identity. Independently built empty environments are equivalent, but
    /// nonempty environments must share persistent storage.
    pub(crate) fn shares_non_memory_storage_with(&self, other: &Self) -> bool {
        fn same_or_empty_map<K, V>(
            left: &std::sync::Arc<std::collections::BTreeMap<K, V>>,
            right: &std::sync::Arc<std::collections::BTreeMap<K, V>>,
        ) -> bool {
            std::sync::Arc::ptr_eq(left, right) || (left.is_empty() && right.is_empty())
        }
        let same_or_empty_resources = |left: &ResourceContext, right: &ResourceContext| {
            (std::sync::Arc::ptr_eq(&left.storage, &right.storage)
                && std::sync::Arc::ptr_eq(&left.loan_dependencies, &right.loan_dependencies))
                || (left.is_pristine_semantically_empty() && right.is_pristine_semantically_empty())
        };
        let same_bindings = match (&self.resource_bindings, &other.resource_bindings) {
            (None, None) => true,
            (Some(left), Some(right)) => same_or_empty_map(left, right),
            _ => false,
        };
        self.population_effects
            .predicate_count_permissions
            .is_some()
            == other
                .population_effects
                .predicate_count_permissions
                .is_some()
            && self.typed_access_policy == other.typed_access_policy
            && same_bindings
            && same_or_empty_map(&self.locals.bindings, &other.locals.bindings)
            && same_or_empty_map(&self.locals.slots, &other.locals.slots)
            && same_or_empty_resources(&self.instance_field_scope, &other.instance_field_scope)
            && same_or_empty_resources(&self.resources, &other.resources)
            && self.loan_ledger == other.loan_ledger
            && self.loan_participant == other.loan_participant
            && self.loan_view_bindings == other.loan_view_bindings
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
        identity: Variable,
        children: &[String],
    ) -> Option<&ResourceInstance> {
        if !children.is_empty() {
            return None;
        }
        self.resource_instance_fields(identity)
    }
    pub(crate) fn resource_instance_fields(&self, identity: Variable) -> Option<&ResourceInstance> {
        let actual = match &self.resource_bindings {
            Some(bindings) => *bindings.get(&identity)?,
            None => identity,
        };
        self.resources
            .owned_instance(actual)
            .or_else(|| self.instance_field_scope.owned_instance(actual))
    }
    pub(crate) fn owned_resource_instance(&self, identity: Variable) -> Option<&ResourceInstance> {
        let actual = match &self.resource_bindings {
            Some(bindings) => *bindings.get(&identity)?,
            None => identity,
        };
        self.resources.owned_instance(actual)
    }
    pub(crate) fn resolve_named_mutex_authority(
        &self,
        identity: Variable,
    ) -> Option<&CResourceFact> {
        self.named_mutex_authorities
            .as_ref()?
            .resolve(identity, self)
    }

    pub(in crate::kernel) fn bind_named_mutex_authority(
        mut self,
        identity: Variable,
        fact: &CResourceFact,
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
        identity: Variable,
        expected: &CResourceFact,
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
        identity: Variable,
        source: &CResourceFact,
        derived: &CResourceFact,
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
                Some(super::super::population_authority::c_creation::CreationEvents::new());
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
        authority: &CResourceFact,
        owned_members: u32,
    ) -> Result<Self, String> {
        let CResourceFact::Own(CResource::PopulationAuthority(description), quantity) = authority
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
            let member = CResourceFact::own(CResource::Composite {
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
            .map_err(|refusal| format!("opaque population import refused: {refusal:?}"))?;
        let mut next = self.clone();
        Arc::make_mut(&mut next.population_effects).creation = Some(events);
        Ok(next)
    }

    pub(crate) fn import_opaque_population_inputs(
        &self,
        authority: &CResourceFact,
    ) -> Result<Self, String> {
        let CResource::PopulationAuthority(description) = authority.resource() else {
            return Err("population import requires authority".into());
        };
        if !description.schema().is_fieldless() {
            if authority
                .owned_quantity_term()
                .and_then(Bitvector32Term::as_const)
                != Some(1)
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
                .map_err(|refusal| format!("named authority import refused: {refusal:?}"))?;
            let mut next = self.clone();
            Arc::make_mut(&mut next.population_effects).creation = Some(events);
            return Ok(next);
        }
        let member = CResourceFact::own(CResource::Composite {
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
                fact.owned_quantity_term()
                    .and_then(Bitvector32Term::as_const)
                    .and_then(|quantity| total.checked_add(quantity))
            })
        {
            // Separate contract clauses, such as a retained `owns` member
            // beside a `consumes` batch, are one custody of their summed units.
            if authority
                .owned_quantity_term()
                .and_then(Bitvector32Term::as_const)
                != Some(1)
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
                    &Bitvector32Term::Constant(total),
                )
                .map_err(|refusal| format!("batch population import refused: {refusal:?}"))?;
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
        authority: &CResourceFact,
        member: &CResourceFact,
    ) -> Result<Self, String> {
        let CResourceFact::Own(CResource::PopulationAuthority(description), authority_quantity) =
            authority
        else {
            return Err("batch import requires owned authority".into());
        };
        let CResourceFact::Own(CResource::Composite { name, arguments }, quantity) = member else {
            return Err("batch import requires an owned declared member quantity".into());
        };
        if authority_quantity.as_const() != Some(1)
            || name != description.family()
            || arguments.as_ref() != description.arguments()
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
            .import_observable_contract_population_quantity(description, quantity)
            .map_err(|refusal| format!("batch population import refused: {refusal:?}"))?;
        let mut next = self.clone();
        Arc::make_mut(&mut next.population_effects).creation = Some(events);
        Ok(next)
    }

    /// Import exactly the authority and identified member declared at a
    /// wildcard helper entry. Neither input is a population creation event.
    pub(crate) fn import_opaque_wildcard_population(
        &self,
        authority: &CResourceFact,
        member: &CResourceFact,
    ) -> Result<Self, String> {
        let CResourceFact::Own(CResource::PopulationAuthority(scope), quantity) = authority else {
            return Err("Requires owns authority(R(anchor, _))".into());
        };
        let CResourceFact::Own(CResource::Composite { name, arguments }, member_quantity) = member
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
            .map_err(|refusal| format!("wildcard population import refused: {refusal:?}"))?;
        let mut next = self.clone();
        Arc::make_mut(&mut next.population_effects).creation = Some(events);
        Ok(next)
    }

    pub(crate) fn import_opaque_wildcard_authority(
        &self,
        authority: &CResourceFact,
    ) -> Result<Self, String> {
        let CResourceFact::Own(CResource::PopulationAuthority(scope), quantity) = authority else {
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
            .map_err(|refusal| format!("wildcard authority import refused: {refusal:?}"))?;
        let mut next = self.clone();
        Arc::make_mut(&mut next.population_effects).creation = Some(events);
        Ok(next)
    }

    pub(crate) fn with_checked_current_control_wrapper(
        &self,
        selected: &CResourceFact,
        definition: &super::super::CCompositeResourceDefinition,
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
    pub(crate) fn tracks_authority_member(&self, selected: &CResourceFact) -> bool {
        let CResource::Composite { name, arguments } = selected.resource() else {
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
        selected: &CResourceFact,
        definition: &super::super::CCompositeResourceDefinition,
        assumptions: &PureFactContext,
    ) -> Result<(ResourceContext, Vec<Bitvector32Term>), String> {
        self.authority_wrapper_fact_projection(selected, definition, assumptions, true)
    }

    /// Closing an open control checks actual owned children, not its suspended
    /// invariant. This projection grants custody reads and publishes no facts.
    pub(crate) fn checked_authority_wrapper_closing_projection(
        &self,
        selected: &CResourceFact,
        definition: &super::super::CCompositeResourceDefinition,
        assumptions: &PureFactContext,
    ) -> Result<(ResourceContext, Vec<Bitvector32Term>), String> {
        self.authority_wrapper_fact_projection(selected, definition, assumptions, false)
    }

    fn authority_wrapper_fact_projection(
        &self,
        selected: &CResourceFact,
        definition: &super::super::CCompositeResourceDefinition,
        assumptions: &PureFactContext,
        require_folded: bool,
    ) -> Result<(ResourceContext, Vec<Bitvector32Term>), String> {
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
            .try_compose_with_facts_delaying_normalization(missing, assumptions)
            .map_err(|error| format!("control body ownership refused: {error:?}"))?;
        Ok((projected, count))
    }

    pub(crate) fn checked_authority_wrapper_body(
        &self,
        selected: &CResourceFact,
        definition: &super::super::CCompositeResourceDefinition,
        assumptions: &PureFactContext,
    ) -> Result<(Vec<CResourceFact>, Vec<Bitvector32Term>), String> {
        self.authority_wrapper_body(selected, definition, assumptions, true)
    }

    /// Describe a selected control's declared authorities for exit checking.
    /// Unlike opening its body, this grants no ownership or count observations.
    pub(in crate::kernel) fn authority_wrapper_descriptions(
        &self,
        selected: &CResourceFact,
        definition: &super::super::CCompositeResourceDefinition,
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
        selected: &CResourceFact,
        definition: &super::super::CCompositeResourceDefinition,
        assumptions: &PureFactContext,
    ) -> Result<Vec<Bitvector32Term>, String> {
        let (_, count) = self.authority_wrapper_body(selected, definition, assumptions, false)?;
        Ok(count)
    }

    fn authority_wrapper_body(
        &self,
        selected: &CResourceFact,
        definition: &super::super::CCompositeResourceDefinition,
        assumptions: &PureFactContext,
        require_folded: bool,
    ) -> Result<(Vec<CResourceFact>, Vec<Bitvector32Term>), String> {
        let (children, descriptions) =
            self.authority_wrapper_candidates(selected, definition, assumptions, require_folded)?;
        let mut counts = Vec::with_capacity(descriptions.len());
        for description in descriptions {
            let [AlgebraicValue::C(CValue::Pointer(pointer))] = description.arguments() else {
                return Err("control authority needs one pointer anchor".into());
            };
            let anchor = pointer.pointer();
            let events = self
                .population_effects
                .creation
                .as_ref()
                .ok_or("control resource requires the creation ledger")?;
            if !events.owns_population_authority(&description) {
                return Err("Requires owns authority(R(p))".into());
            }
            let count = if anchor.block != PointerBlock::ExternalArgument
                && anchor.offset == PointerOffsetTerm::Constant(0)
            {
                events
                    .observe_term(&anchor.block, description.family())
                    .map_err(|_| "Requires a current authority count")?
            } else {
                let imported = events
                    .observe_symbolic(&description)
                    .ok_or("Requires a current authority count")?;
                if let Some((produce, quantity)) = imported.combined_delta() {
                    if produce {
                        Bitvector32Term::add(imported.entry_count, quantity)
                    } else {
                        Bitvector32Term::subtract(imported.entry_count, quantity)
                    }
                } else {
                    match imported.delta.cmp(&0) {
                        std::cmp::Ordering::Equal => imported.entry_count,
                        std::cmp::Ordering::Greater => Bitvector32Term::add(
                            imported.entry_count,
                            Bitvector32Term::Constant(imported.delta.unsigned_abs()),
                        ),
                        std::cmp::Ordering::Less => Bitvector32Term::subtract(
                            imported.entry_count,
                            Bitvector32Term::Constant(imported.delta.unsigned_abs()),
                        ),
                    }
                }
            };
            counts.push(count);
        }
        Ok((children, counts))
    }

    /// A standalone helper's typed lock returns a fresh authority-bearing
    /// control. Its contained authority enters this proof as an arbitrary
    /// existing population: a fresh total, bounded below only by the members
    /// already owned here, with no creator right. Each population may enter
    /// once per proof, so a later acquisition cannot reuse an earlier total.
    pub(crate) fn import_acquired_control_authorities(
        &self,
        instance: &super::super::ResourceInstance,
        definition: &super::super::CCompositeResourceDefinition,
        assumptions: &PureFactContext,
    ) -> Result<Self, String> {
        if !definition.contains().iter().any(|spec| {
            matches!(
                spec.term(),
                super::super::CResourceTerm::PopulationAuthority { .. }
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
                super::super::CResourceTerm::PopulationAuthority { .. }
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
            .map_err(|_| "could not evaluate the acquired control authority")?;
            let CResource::PopulationAuthority(description) = authority.resource() else {
                return Err("could not evaluate the acquired control authority".into());
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
            let member = CResourceFact::own(CResource::Composite {
                name: description.family().to_owned(),
                arguments: description.arguments().to_vec().into(),
            });
            let owned = next
                .resources
                .exact_resource_facts(member.resource())
                .into_iter()
                .filter_map(|fact| {
                    fact.owned_quantity_term()
                        .and_then(Bitvector32Term::as_const)
                })
                .sum::<u32>();
            let events = events
                .import_acquired_control_population(description, owned)
                .map_err(|refusal| format!("acquired control authority refused: {refusal:?}"))?;
            Arc::make_mut(&mut next.population_effects).creation = Some(events);
        }
        Ok(next)
    }

    /// A standalone helper assumes a folded control from its caller. Only the
    /// checked body of that exact owned wrapper may seed its opaque population
    /// inputs; no direct authority or creator right is manufactured here.
    pub(crate) fn import_opaque_control_wrapper(
        &self,
        selected: &CResourceFact,
        definition: &super::super::CCompositeResourceDefinition,
        assumptions: &PureFactContext,
        wildcard_members: &std::collections::BTreeMap<
            super::super::ResourceDescription,
            Vec<CResourceFact>,
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
        selected: &CResourceFact,
        definition: &super::super::CCompositeResourceDefinition,
        assumptions: &PureFactContext,
    ) -> Result<Vec<(ResourceDescription, Option<Bitvector32Term>)>, String> {
        if !self.resources.contains_exact_representation(selected) {
            return Err("Requires the declared owned control resource".into());
        }
        let (children, descriptions) =
            self.authority_wrapper_candidates(selected, definition, assumptions, true)?;
        let mut components = Vec::with_capacity(descriptions.len());
        for description in &descriptions {
            let [AlgebraicValue::C(CValue::Pointer(anchor_value))] = description.arguments() else {
                return Err("control authority needs one pointer anchor".into());
            };
            let anchor = anchor_value.pointer().clone();
            let CResourceFact::Own(CResource::Composite { arguments, .. }, _) = selected else {
                return Err("Requires owns control resource".into());
            };
            if arguments.as_ref() != description.arguments() || definition.parameters().len() != 1 {
                return Err("control and authority need the same pointer argument".into());
            }
            let parameter = definition.parameters()[0].name();
            let memory_cells = children
                .iter()
                .filter_map(CResourceFact::memory_own_range)
                .collect::<Vec<_>>();
            let allocations = children
                .iter()
                .filter_map(CResourceFact::allocation)
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
            let is_parameter = |expression: &SpecExpression| matches!(expression, SpecExpression::CExpression(CExpression::Variable(name)) if name == parameter);
            let is_counter_load = |expression: &SpecExpression| {
                let SpecExpression::MemoryLoad {
                    memory: SpecMemory::Current,
                    pointer,
                    value_type: CType::Int32,
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
                            && matches!(elements.as_ref(), SpecExpression::Value(CValue::Int32(zero)) if zero.as_const() == Some(0))
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
            operator: CComparisonOperator::Equal,
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
                Some(Bitvector32Term::MemoryLoad(
                    intern_c_memory_ref(&self.memory),
                    Box::new(anchor.clone()),
                    LoadKind::Bits32,
                )),
            ));
        }
        Ok(components)
    }

    fn authority_wrapper_candidates(
        &self,
        selected: &CResourceFact,
        definition: &super::super::CCompositeResourceDefinition,
        assumptions: &PureFactContext,
        require_folded: bool,
    ) -> Result<(Vec<CResourceFact>, Vec<ResourceDescription>), String> {
        let CResourceFact::Own(CResource::Composite { name, arguments }, quantity) = selected
        else {
            return Err("Requires owns control resource".into());
        };
        if name != definition.name()
            || quantity.as_const() != Some(1)
            || (require_folded && !self.resources.satisfies_fact(selected, assumptions))
            || definition.parameters().len() != arguments.len()
            || definition
                .instance_schema
                .as_ref()
                .is_some_and(|schema| !schema.fields().is_empty())
            || definition.matched.is_some()
            || !definition.witnesses.is_empty()
            || definition.condition.is_some()
            || !definition.children.is_empty()
            || !definition.resource_parameters.is_empty()
        {
            return Err("Requires one folded authority control resource".into());
        }
        let mut evaluation = CState::new().with_memory(self.memory.clone());
        evaluation.population_effects = self.population_effects.clone();
        for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
            let value = argument
                .as_c_value()
                .ok_or("control resource needs concrete arguments")?;
            if parameter.c_type() != value.c_type() {
                return Err("control resource argument has the wrong type".into());
            }
            evaluation.locals.set_typed(
                parameter.name().to_string(),
                value.clone(),
                parameter.c_type(),
            );
        }
        let mut children = Vec::with_capacity(definition.contains().len());
        let mut authorities = Vec::new();
        let mut seen_authorities = std::collections::BTreeSet::new();
        let mut budget = ExecutionBudget::beside_live_state();
        for spec in definition.contains() {
            if spec.access() != super::super::CResourceAccessMode::Own
                || spec.quantity() != &super::super::CResourceQuantity::One
                || spec.guard().is_some()
                || !spec.resource_arguments().is_empty()
            {
                return Err("control body requires exact owned resources".into());
            }
            let child = match spec.term() {
                super::super::CResourceTerm::PopulationAuthority { .. } => {
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
                    .map_err(|error| format!("control authority evaluation failed: {error:?}"))?
                    .map_err(|error| format!("control authority evaluation failed: {error:?}"))?
                }
                super::super::CResourceTerm::Memory(_) => {
                    super::super::functions::evaluate_function_resource_spec(
                        &evaluation,
                        spec,
                        assumptions,
                        &mut budget,
                    )
                    .map_err(|error| format!("control memory evaluation failed: {error:?}"))?
                    .map_err(|error| format!("control memory evaluation failed: {error:?}"))?
                }
                super::super::CResourceTerm::Token { name, .. }
                    if name == CResourceFact::ALLOCATION_RESOURCE_NAME =>
                {
                    super::super::functions::evaluate_function_resource_spec(
                        &evaluation,
                        spec,
                        assumptions,
                        &mut budget,
                    )
                    .map_err(|error| format!("control allocation evaluation failed: {error:?}"))?
                    .map_err(|error| format!("control allocation evaluation failed: {error:?}"))?
                }
                _ => {
                    return Err(
                        "control body supports owned memory, allocation, and authorities".into(),
                    );
                }
            };
            if let CResource::PopulationAuthority(description) = child.resource() {
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
                    CResource::Memory(_) => "memory",
                    CResource::PopulationAuthority(_) => "population authority",
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
    pub(in crate::kernel) fn population_storage_created_here(&self, pointer: &Pointer) -> bool {
        pointer.offset == PointerOffsetTerm::Constant(0)
            && (matches!(&pointer.block, PointerBlock::Heap(_))
                && self.memory.live_heap_block_size(pointer).is_some()
                || pointer.block.starts_with("local:") && self.memory.has_block(&pointer.block))
            && self
                .population_effects
                .creation
                .as_ref()
                .is_some_and(|events| events.created_here(&pointer.block))
    }

    /// The only state transition that creates or retires a population
    /// authority resource. The event ledger owns the abstract population
    /// identity and its zero-count retirement check; the resource algebra
    /// checks exclusive possession of the visible fact.
    pub(crate) fn checked_population_authority_exchange(
        &self,
        selected: &CResourceFact,
        establish: bool,
        assumptions: &PureFactContext,
    ) -> Result<(CState, CheckedPopulationAuthorityExchange), String> {
        if self
            .population_effects
            .predicate_count_permissions
            .is_some()
        {
            return Err("predicate count snapshots cannot change authority".into());
        }
        let CResourceFact::Own(CResource::PopulationAuthority(description), quantity) = selected
        else {
            return Err("Requires owns authority(R(p))".into());
        };
        if quantity.as_const() != Some(1) {
            return Err("Requires one authority(R(p))".into());
        }
        let [AlgebraicValue::C(CValue::Pointer(pointer))] = description.arguments() else {
            return Err("authority requires one pointer anchor".into());
        };
        let anchor = pointer.pointer();
        let events = self
            .population_effects
            .creation
            .as_ref()
            .ok_or("the state has no creation history")?;
        let imported_retirement = !establish
            && anchor.block == PointerBlock::ExternalArgument
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
            && (anchor.offset != PointerOffsetTerm::Constant(0)
                || !(matches!(&anchor.block, PointerBlock::Heap(_))
                    && self.memory.live_heap_block_size(anchor).is_some()
                    || anchor.block.starts_with("local:") && self.memory.has_block(&anchor.block)))
        {
            return Err("Requires live base storage for authority(R(p))".into());
        }
        let mut next = self.clone();
        let evidence = if establish {
            let (history, evidence) = events
                .checked_establish(&anchor.block, description)
                .map_err(|refusal| format!("authority establishment refused: {refusal:?}"))?;
            let resources = self
                .resources
                .clone()
                .try_compose_with_fact(selected.clone(), assumptions)
                .map_err(|error| format!("authority ownership refused: {error:?}"))?;
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
                events.checked_retire(&anchor.block, description)
            }
            .map_err(|refusal| format!("authority retirement refused: {refusal:?}"))?;
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
        selected: &CResourceFact,
        produce: bool,
        definition: &super::super::CCompositeResourceDefinition,
        assumptions: &PureFactContext,
    ) -> Result<(CState, CheckedPopulationMemberExchange), String> {
        if self
            .population_effects
            .predicate_count_permissions
            .is_some()
        {
            return Err("predicate count snapshots cannot change membership".into());
        }
        let CResourceFact::Own(CResource::Composite { name, arguments }, quantity) = selected
        else {
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
                    super::super::CResourceTerm::Memory(_)
                        | super::super::CResourceTerm::Token { .. }
                        | super::super::CResourceTerm::Composite { .. }
                ) || spec.access() != super::super::CResourceAccessMode::Own
                    || spec.quantity() != &super::super::CResourceQuantity::One
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
        let Some(AlgebraicValue::C(CValue::Pointer(pointer))) = description.arguments().first()
        else {
            return Err("Requires an exact pointer-anchored authorized resource R(p)".into());
        };
        let anchor = pointer.pointer();
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
            && (anchor.offset != PointerOffsetTerm::Constant(0)
                || !(matches!(&anchor.block, PointerBlock::Heap(_))
                    && self.memory.live_heap_block_size(anchor).is_some()
                    || anchor.block.starts_with("local:") && self.memory.has_block(&anchor.block)))
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
        let authority = CResourceFact::own(CResource::PopulationAuthority(governing.clone()));
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
                &self.memory,
                assumptions,
            )
            .ok_or("cannot instantiate the member's private body")?;
            expanded.facts().to_vec()
        };
        for child in &body {
            let Some(range) = child.memory_own_range() else {
                if let CResourceFact::Own(
                    CResource::Token { .. } | CResource::Composite { .. },
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
            if !imported_member_exchange
                && !self.memory.access_in_bounds(&base, bytes)
                && !assumptions.proves_memory_loadable_for_memory_resolution(
                    &self.memory,
                    &base,
                    &Bitvector32Term::Constant(bytes),
                )
            {
                return Err("member private memory exceeds live storage".into());
            }
            if let Some(ledger) = self.loan_ledger() {
                ledger
                    .permits_memory_access_with_assumptions(range, assumptions)
                    .map_err(|_| "member private memory has an active borrow")?;
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
                .map_err(|error| format!("member ownership refused: {error:?}"))?
        } else {
            let resources = self
                .resources
                .clone()
                .without_fact_incrementally(selected, assumptions)
                .ok_or_else(|| format!("Requires owns {name}(p)"))?;
            resources
                .try_compose_with_facts_delaying_normalization(body.iter().cloned(), assumptions)
                .map_err(|error| format!("member body ownership refused: {error:?}"))?
        };
        let exchange = if definition.has_fixed_exclusive_memory() {
            events.checked_exclusive_member_exchange_quantity(
                &anchor.block,
                &description,
                produce,
                quantity,
                assumptions,
            )
        } else {
            events.checked_member_exchange_quantity(
                &anchor.block,
                &description,
                produce,
                quantity,
                assumptions,
            )
        };
        let (history, evidence) = exchange
            .map_err(|error| {
                if produce && governing.population_arity().is_some()
                    && events.observe_symbolic(&governing).is_some()
                    && matches!(error, super::super::population_authority::c_creation::CreationRefusal::InvalidQuantity)
                {
                    format!("Requires defined(count({name}({}, {})) + 1)", definition.parameters().first().map_or("anchor", |parameter| parameter.name()),
                        std::iter::repeat_n("_", arguments.len() - 1).collect::<Vec<_>>().join(", "))
                } else { format!("member change refused: {error:?}") }
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
        before: &CState,
        instance: &super::super::ResourceInstance,
        produce: bool,
        assumptions: &PureFactContext,
    ) -> Result<(), String> {
        if before
            .population_effects
            .predicate_count_permissions
            .is_some()
        {
            return Err("predicate count snapshots cannot change named membership".into());
        }
        let Some(events) = &before.population_effects.creation else {
            return Ok(());
        };
        let description = super::super::ResourceDescription::from_instance(instance);
        let history = if events.tracks_population(&description) {
            let governing = events
                .governing_authority(&description)
                .ok_or("Requires a matching population authority")?;
            let authority = CResourceFact::own(CResource::PopulationAuthority(governing.clone()));
            if !before.resources.satisfies_fact(&authority, assumptions) {
                return Err(format!("Requires owns authority({}(...))", instance.name()));
            }
            let reference = super::super::ResourceReference::from_instance(instance);
            if events.recognizes_imported_population(&description) {
                let owned = CResourceFact::own(CResource::Instance(instance.clone()));
                if !produce && !before.resources.satisfies_fact(&owned, assumptions) {
                    return Err("Requires owning the exact named member before consumption".into());
                }
                events
                    .checked_imported_instance_exchange(instance, produce, assumptions)
                    .map_err(|refusal| format!("named member change refused: {refusal:?}"))?
            } else {
                events
                    .checked_instance_exchange(&reference, produce)
                    .map_err(|refusal| format!("named member change refused: {refusal:?}"))?
            }
        } else if produce {
            let Some(AlgebraicValue::C(CValue::Pointer(pointer))) = description.arguments().first()
            else {
                return Ok(());
            };
            events.member_created(&pointer.pointer().block, description.family())
        } else {
            return Ok(());
        };
        Arc::make_mut(&mut self.population_effects).creation = Some(history);
        Ok(())
    }

    pub(in crate::kernel) fn record_population_storage_creation(&mut self, block: PointerBlock) {
        if let Some(events) = &self.population_effects.creation {
            Arc::make_mut(&mut self.population_effects).creation = Some(events.created(block));
        }
    }

    pub(in crate::kernel) fn record_pending_population_storage_creation(
        &mut self,
        block: PointerBlock,
    ) {
        if let Some(events) = &self.population_effects.creation {
            Arc::make_mut(&mut self.population_effects).creation =
                Some(events.pending_creation(block));
        }
    }

    pub(in crate::kernel) fn resolve_pending_population_storage_creation(
        &mut self,
        pending_block: &PointerBlock,
        live_block: Option<PointerBlock>,
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
        block: &PointerBlock,
    ) -> Result<(), CRuntimeError> {
        if let Some(events) = &self.population_effects.creation {
            let next = events.retired(block).map_err(|refusal| {
                CRuntimeError::FunctionContract(format!(
                    "population authority prevents storage retirement: {refusal:?}"
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
        blocks: &[PointerBlock],
    ) -> Result<Option<super::super::population_authority::c_creation::CreationEvents>, CRuntimeError>
    {
        let Some(mut events) = self.population_effects.creation.clone() else {
            return Ok(None);
        };
        for block in blocks {
            events = events.retired(block).map_err(|refusal| {
                CRuntimeError::FunctionContract(format!(
                    "population authority prevents storage retirement: {refusal:?}"
                ))
            })?;
        }
        Ok(Some(events))
    }

    pub(in crate::kernel) fn population_storage_retirement_refusal(
        &self,
        block: &PointerBlock,
    ) -> Option<CRuntimeError> {
        self.population_effects
            .creation
            .as_ref()
            .and_then(|events| events.retirement_refusal(block))
            .map(|refusal| {
                CRuntimeError::FunctionContract(format!(
                    "population authority prevents storage {block:?} retirement: {refusal:?}"
                ))
            })
    }

    /// Recover caller environment identity while retaining any creation
    /// events produced by a body that actually executed.
    pub(in crate::kernel) fn restore_population_creation_after_call(
        &mut self,
        caller: Option<&super::super::population_authority::c_creation::CreationEvents>,
        callee: Option<&super::super::population_authority::c_creation::CreationEvents>,
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
            && match (&self.loan_ledger, &other.loan_ledger) {
                (None, None) => true,
                (Some(left), Some(right)) => left.shares_storage_with(right),
                _ => false,
            }
            && self.loan_participant == other.loan_participant
            && self.loan_view_bindings == other.loan_view_bindings
            && self
                .observed_population_families
                .shares_storage_with(&other.observed_population_families)
    }

    pub fn with_local(mut self, name: impl Into<String>, value: CValue) -> Self {
        self.locals.set(name, value);
        self
    }

    pub fn with_memory(mut self, memory: CMemory) -> Self {
        self.set_memory(memory);
        self
    }

    /// Replace the memory snapshot after proof-only cell naming.
    ///
    /// Materializing a canonical load does not write program memory or
    /// invalidate an existing view. The ordinary [`Self::with_memory`] path
    /// deliberately invalidates memory-dependent projections for evaluator
    /// writes, but using it for this proof representation step would discard
    /// unrelated resource views and make a resource rewrite appear to change
    /// more authority than its definition exchanges.
    pub(crate) fn with_materialized_memory(mut self, memory: CMemory) -> Self {
        self.memory = memory;
        self
    }

    /// Replace memory through the single checked-state transition hook.
    /// Keeping this beside `with_memory` prevents evaluator paths that already
    /// own a mutable state from bypassing resource-observation invalidation.
    /// Whether `self == other`, for two states whose memories were each
    /// derived from `base` by persistent updates, as the abstractions of two
    /// arms are derived from the memory at their split. The memories are
    /// compared by what each changed from `base`
    /// ([`CMemory::eq_relative_to`]), so the cost is the arms' changes; the
    /// answer is exact whatever the memories share.
    pub(crate) fn eq_with_memories_from(&self, other: &Self, base: &CMemory) -> bool {
        if !self.memory.eq_relative_to(&other.memory, base) {
            return false;
        }
        // The memories are equal, so the rest is compared with one memory
        // standing on both sides, where it is equal by identity.
        let mut other = other.clone();
        other.memory = self.memory.clone();
        *self == other
    }

    pub(crate) fn set_memory(&mut self, memory: CMemory) {
        self.set_memory_with_checked_stores(memory, false);
    }

    /// [`Self::set_memory`] for the C store path, which has already applied
    /// the iterated-ownership store rule (`plan_iterated_guard_store`) to its
    /// one store. Every other transition keeps the conservative rule.
    pub(crate) fn set_memory_with_checked_stores(&mut self, memory: CMemory, stores_checked: bool) {
        self.resources = self
            .resources
            .clone()
            .invalidate_memory_support(&self.memory, &memory)
            .invalidate_iterated_facts(&self.memory, &memory, stores_checked);
        self.loan_view_bindings = crate::kernel::loans::LoanViewBindings::from_state(
            self.resources.loan_dependency_state(),
        );
        self.memory = memory;
    }

    pub fn with_resource_context(mut self, resources: ResourceContext) -> Self {
        // ResourceContext owns the canonical persistent dependency root. The
        // CState field is only a shared mirror, so replacing a context does
        // not scan unrelated resources or active loans.
        self.loan_view_bindings =
            crate::kernel::loans::LoanViewBindings::from_state(resources.loan_dependency_state());
        self.resources = resources;
        self
    }

    /// Replace resource representation and install checked dependencies for
    /// occurrences created by that rewrite.  The destination occurrences are
    /// supplied by the resource algebra; this method never derives them from
    /// equal facts or from the active ledger.
    pub(crate) fn with_resource_context_and_loan_dependencies(
        mut self,
        resources: ResourceContext,
        dependencies: impl IntoIterator<
            Item = (
                crate::kernel::primitives::ResourceOccurrenceId,
                crate::kernel::loans::LoanViewBinding,
            ),
        >,
    ) -> Self {
        self = self.with_resource_context(resources);
        for (occurrence, binding) in dependencies {
            self.resources = self
                .resources
                .with_loan_dependency(occurrence, binding.clone());
        }
        self.loan_view_bindings = crate::kernel::loans::LoanViewBindings::from_state(
            self.resources.loan_dependency_state(),
        );
        self
    }
    pub(crate) fn loan_ledger(&self) -> Option<&crate::kernel::loans::LoanLedger> {
        self.loan_ledger.as_ref()
    }
    pub(crate) fn with_loan_ledger(
        mut self,
        ledger: Option<crate::kernel::loans::LoanLedger>,
    ) -> Self {
        self.loan_ledger = ledger;
        self
    }

    pub(crate) fn loan_participant(&self) -> Option<crate::kernel::loans::LoanParticipantId> {
        self.loan_participant
    }

    pub(crate) fn with_loan_participant(
        mut self,
        participant: Option<crate::kernel::loans::LoanParticipantId>,
    ) -> Self {
        self.loan_participant = participant;
        self
    }

    pub(crate) fn loan_view_bindings(&self) -> &crate::kernel::loans::LoanViewBindings {
        &self.loan_view_bindings
    }

    /// The resource-context sidecar is canonical.  The legacy ledger map is
    /// kept as a mechanically synchronized mirror for call planning and must
    /// agree in both directions before a checked resource transition runs.
    pub(crate) fn loan_bindings_are_consistent(&self) -> bool {
        let resources_state = self.resources.loan_dependency_state();
        let mirror_state = self.loan_view_bindings.state();
        (resources_state.map.is_empty() && mirror_state.map.is_empty())
            || std::sync::Arc::ptr_eq(&resources_state, &mirror_state)
    }

    pub(crate) fn with_loan_view_bindings(
        mut self,
        bindings: crate::kernel::loans::LoanViewBindings,
    ) -> Self {
        self.loan_view_bindings = bindings;
        self.resources = self
            .resources
            .clone()
            .with_loan_dependency_state(self.loan_view_bindings.state());
        self
    }

    /// The bounded explanation of a refused access, or `None` when the
    /// access is permitted or no ledger is active.
    pub(crate) fn stable_loan_memory_access_refusal(
        &self,
        range: &CMemoryRange,
        assumptions: &PureFactContext,
        operation: crate::kernel::LoanRefusalOperation,
    ) -> Option<crate::kernel::LoanRefusalDiagnostic> {
        self.loan_ledger
            .as_ref()
            .and_then(|ledger| ledger.memory_access_refusal(range, assumptions, operation))
    }

    pub fn locals(&self) -> &CLocalEnvironment {
        &self.locals
    }

    pub(crate) fn local_object_type(&self, name: &str) -> Option<CType> {
        self.locals.object_type(name)
    }

    pub(crate) fn global_object_type(&self, name: &str) -> Option<CType> {
        self.locals
            .is_global_object(name)
            .then(|| self.locals.object_type(name))
            .flatten()
    }

    pub(crate) fn global_array_element_type(&self, name: &str) -> Option<CType> {
        self.locals
            .is_array_object(name)
            .then(|| self.locals.object_type(name))
            .flatten()
    }

    pub fn memory(&self) -> &CMemory {
        &self.memory
    }

    /// The value one scalar local or parameter holds now, by name: a stored
    /// local's slot cell, or a logical parameter's binding, which no store
    /// can change. Nothing when a stored slot's cell is not known.
    pub(crate) fn scalar_local_value(&self, name: &str) -> Option<CValue> {
        match self.locals.binding(name)? {
            CLocalBinding::Object {
                storage_declared: false,
                value,
                slot,
                ..
            } => self
                .memory
                .known_value(slot)
                .or_else(|| Some(value.clone())),
            CLocalBinding::Object { slot, .. } => self.memory.known_value(slot),
            _ => None,
        }
    }

    /// The values held by memory-resident scalar locals at offset zero.
    /// Resolve names through the local-slot index so framed parameter blocks
    /// are exposed with their source name rather than their internal block id.
    pub fn local_cell_values(&self) -> impl Iterator<Item = (&str, CValue)> + '_ {
        // A local's slot is at offset zero of its block, so a run holds one
        // only at the slot spelled that way, looked up rather than visited.
        let run_slots = self.memory.cells.runs().filter_map(|run| {
            let pointer = Pointer {
                block: run.base().block.clone(),
                offset: PointerOffsetTerm::Constant(0),
            };
            let index = run.live_slot_index(&pointer)?;
            Some((pointer, run.value(index)))
        });
        let mut values = self
            .memory
            .cells
            .concrete()
            .iter()
            .filter(|(pointer, _)| pointer.offset == PointerOffsetTerm::Constant(0))
            .map(|(pointer, value)| (pointer.clone(), value.clone()))
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
    pub(crate) fn local_name_holding_bitvector_variable(&self, variable: Variable) -> Option<&str> {
        for (pointer, name) in self.locals.slots.iter() {
            if crate::instrumentation::deadline_exceeded() {
                return None;
            }
            crate::instrumentation::record_deterministic_work(1);
            if pointer.offset == PointerOffsetTerm::Constant(0)
                && self.memory.cells.bitvector_variable_at(pointer) == Some(variable)
            {
                return Some(name.as_str());
            }
        }
        None
    }

    /// An atom's recorded load address selects one local slot directly.
    pub(crate) fn local_name_holding_bitvector_variable_at(
        &self,
        variable: Variable,
        pointer: &Pointer,
    ) -> Option<&str> {
        if crate::instrumentation::deadline_exceeded() {
            return None;
        }
        let name = self.locals.name_for_slot(pointer)?;
        (self.memory.cells.bitvector_variable_at(pointer) == Some(variable)).then_some(name)
    }

    /// Refresh caller scalar bindings after call-site code has modified their
    /// address-backed cells. Ordinary function frames keep their own local
    /// environment, but inline bodies execute with a separate parameter
    /// environment while retaining the caller's memory.
    pub(in crate::kernel) fn sync_scalar_locals_from_memory(&mut self, memory: &CMemory) {
        let updates = self
            .locals
            .bindings
            .iter()
            .filter_map(|(name, binding)| {
                let (c_type, slot, volatile, pointee_volatile, constant, pointee_constant) =
                    match binding {
                        CLocalBinding::Object {
                            c_type,
                            slot,
                            volatile,
                            pointee_volatile,
                            constant,
                            pointee_constant,
                            ..
                        }
                        | CLocalBinding::UninitializedObject {
                            c_type,
                            slot,
                            volatile,
                            pointee_volatile,
                            constant,
                            pointee_constant,
                            ..
                        } => (
                            *c_type,
                            slot.clone(),
                            *volatile,
                            *pointee_volatile,
                            *constant,
                            *pointee_constant,
                        ),
                        CLocalBinding::GlobalObject { .. }
                        | CLocalBinding::ArrayObject { .. }
                        | CLocalBinding::AggregateObject { .. } => return None,
                    };
                memory
                    .known_value(&slot)
                    .filter(|value| {
                        c_type.accepts(value)
                            || !matches!(binding, CLocalBinding::UninitializedObject { .. })
                    })
                    .map(|value| {
                        (
                            name.clone(),
                            value,
                            c_type,
                            slot,
                            volatile,
                            pointee_volatile,
                            constant,
                            pointee_constant,
                        )
                    })
            })
            .collect::<Vec<_>>();
        for (name, value, c_type, slot, volatile, pointee_volatile, constant, pointee_constant) in
            updates
        {
            self.locals.set_typed_qualified_with_all_qualifiers(
                name,
                value,
                c_type,
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
    /// Predicate memory arguments retain their existing, explicit snapshot
    /// representation. Keeping memory and locals out of this value prevents
    /// an unrelated C step from changing the identity of a predicate merely
    /// because the predicate language can also observe resource counts.
    pub fn resource_state_snapshot(&self) -> Self {
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
    static BLOCK_ALIGNMENT_REGISTRY: std::cell::RefCell<BTreeMap<PointerBlock, u64>> =
        const { std::cell::RefCell::new(BTreeMap::new()) };
}

thread_local! {
    /// Where the argument copied into each by-value aggregate parameter's
    /// frame block arrived. The callee's copy and the caller's argument are
    /// two objects; a diagnostic reads this to name the second. Nothing
    /// that decides a proof reads it.
    static AGGREGATE_ARGUMENT_SOURCES: std::cell::RefCell<BTreeMap<PointerBlock, Pointer>> =
        const { std::cell::RefCell::new(BTreeMap::new()) };
}

/// Records that the aggregate parameter stored in `slot` was copied from
/// `source`. One entry per parameter bound; a later binding of the same
/// frame block replaces it.
pub(crate) fn register_aggregate_argument_source(slot: &PointerBlock, source: &Pointer) {
    AGGREGATE_ARGUMENT_SOURCES.with(|sources| {
        sources.borrow_mut().insert(slot.clone(), source.clone());
    });
}

pub(crate) fn registered_aggregate_argument_source(slot: &PointerBlock) -> Option<Pointer> {
    AGGREGATE_ARGUMENT_SOURCES.with(|sources| sources.borrow().get(slot).cloned())
}

pub(crate) fn register_block_alignment(block: &PointerBlock, alignment: u32) {
    if alignment < 2 {
        return;
    }
    BLOCK_ALIGNMENT_REGISTRY.with(|registry| {
        registry
            .borrow_mut()
            .insert(block.clone(), u64::from(alignment));
    });
}

pub(crate) fn registered_block_alignment(block: &PointerBlock) -> Option<u64> {
    BLOCK_ALIGNMENT_REGISTRY.with(|registry| registry.borrow().get(block).copied())
}

/// Look up an intrinsic block alignment after charging the bounded key
/// payload and logarithmic ordered-map search. Callers must validate the key
/// payload before invoking this helper; the charge here accounts for the
/// registry lookup itself and never scans unrelated entries.
pub(crate) fn registered_block_alignment_charged(
    block: &PointerBlock,
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
    alignment: BTreeMap<PointerBlock, u64>,
    never_address_taken: BTreeSet<String>,
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
    /// The names of automatic objects — locals and parameters — whose address
    /// no function in this session's C sources ever takes, and which are
    /// declared everywhere with a scalar or pointer type.
    ///
    /// Deliberately a set of *names*, not of blocks. A block identity says
    /// nothing about which function declared it (`local:x` in `f` and in `g`
    /// are one spelling), and the resolution memo and the canonical-load
    /// projection cache are scoped to a verification rather than to a
    /// function. An answer that differed between two functions of one session
    /// would therefore be cached under the first function's answer and served
    /// to the second. Indexing by name makes the answer function-independent:
    /// a name taken in *any* function is absent for *every* function, which
    /// loses proofs about the innocent one and can never serve a stale answer.
    ///
    /// Populated once, before any query, by the surface's pre-pass over every
    /// parsed function body, and emptied when a session starts. Absence is the
    /// answer for everything else, including the verifier's own synthetic
    /// names, so an unpopulated registry decides nothing.
    static NEVER_ADDRESS_TAKEN_LOCALS_KEY: std::cell::RefCell<std::sync::Arc<()>> = std::cell::RefCell::new(std::sync::Arc::new(()));
    static NEVER_ADDRESS_TAKEN_LOCALS: std::cell::RefCell<BTreeSet<String>> =
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
/// `never_address_taken_local_names`.
pub(crate) fn never_address_taken_locals_key() -> std::sync::Arc<()> {
    NEVER_ADDRESS_TAKEN_LOCALS_KEY.with(|key| key.borrow().clone())
}

pub(crate) fn set_never_address_taken_locals(names: BTreeSet<String>) {
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
pub(crate) fn withdraw_never_address_taken_locals(taken: &BTreeSet<String>) -> bool {
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

/// The automatic object a `local:` block holds, as the program names it, or
/// `None` when the spelling is not one automatic object's.
///
/// Three spellings reach a `local:` block: `local:x` for a declaration,
/// `local:lifetime:2:x` for a re-entered one, and `local:frame:3:x` for a
/// call frame's. A C identifier contains no colon, so the forms cannot be
/// confused with a local genuinely named `frame` or `lifetime`, and any other
/// shape is refused rather than guessed.
fn local_block_object_name(block: &PointerBlock) -> Option<&str> {
    let rest = block.strip_prefix("local:")?;
    match rest.split_once(':') {
        None => Some(rest),
        Some(("lifetime" | "frame", tail)) => {
            let (_, name) = tail.split_once(':')?;
            (!name.contains(':')).then_some(name)
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
/// (`CMemoryCanStore` / `access_in_bounds`), and an integer cast to a pointer
/// is outside the supported C0 subset. A `&x` written in a *proof* creates no
/// runtime pointer, so an annotation cannot make an object addressable that
/// the program never addresses.
///
/// This is therefore a claim about addressability, not about one pair of
/// pointers: a never-address-taken object is not memory any pointer value can
/// designate. The caller must still defer to an equality the context *states*
/// about the pointer, because an assumed `p == &x` would otherwise be refuted
/// and the context silently made inconsistent.
pub(crate) fn block_is_never_address_taken_local(block: &PointerBlock) -> bool {
    let Some(name) = local_block_object_name(block) else {
        return false;
    };
    NEVER_ADDRESS_TAKEN_LOCALS.with(|registry| registry.borrow().contains(name))
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
        set_never_address_taken_locals(BTreeSet::from(["hidden".to_string()]));
        let hidden: PointerBlock = "local:hidden".into();
        let taken: PointerBlock = "local:taken".into();
        for value in [
            PointerBlock::Symbolic(Variable(7)),
            PointerBlock::FunctionSymbolic(Variable(8)),
            PointerBlock::ExternalObject(Variable(9)),
            PointerBlock::ExternalArgument,
        ] {
            assert!(value.proven_distinct(&hidden), "{value:?}");
            assert!(hidden.proven_distinct(&value), "{value:?}");
        }
        assert!(!PointerBlock::Symbolic(Variable(7)).proven_distinct(&taken));
        clear_never_address_taken_locals();
        assert!(!PointerBlock::Symbolic(Variable(7)).proven_distinct(&hidden));
    }
}

#[cfg(test)]
mod contract_retirement_tests {
    use super::*;

    #[test]
    fn retirement_drops_zeroed_status_under_each_equal_base_spelling() {
        let base = Pointer {
            block: PointerBlock::Heap(922_200),
            offset: PointerOffsetTerm::Constant(0),
        };
        let aliases = [
            Pointer {
                block: PointerBlock::Symbolic(Variable(922_201)),
                offset: PointerOffsetTerm::Constant(0),
            },
            Pointer {
                block: PointerBlock::Symbolic(Variable(922_202)),
                offset: PointerOffsetTerm::Constant(4),
            },
        ];
        let unrelated = Pointer {
            block: PointerBlock::Heap(922_203),
            offset: PointerOffsetTerm::Constant(0),
        };
        let assumptions = aliases.iter().fold(PureFactContext::new(), |facts, alias| {
            facts.assume_proposition(Proposition::ConditionIs(
                ConditionTerm::pointer_equal(alias.clone(), base.clone()),
                true,
            ))
        });
        let mut memory = CMemory::new()
            .with_heap_allocation_claim(base.clone(), 4)
            .expect("fresh input allocation");
        let heap = std::sync::Arc::make_mut(&mut memory.heap);
        heap.zeroed_allocations.extend(aliases.iter().cloned());
        heap.zeroed_allocations.insert(unrelated.clone());
        memory = memory.store_with_context(aliases[0].clone(), int32(9), &assumptions);
        memory = memory.store(unrelated.clone(), int32(11));
        assert!(memory.has_initialized_bytes_at(&aliases[0], 4));
        let retired = memory.retire_contract_heap_allocation_claim(
            &base,
            &Bitvector32Term::Constant(4),
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
        let base = Pointer {
            block: PointerBlock::Concrete("local:u".to_string()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = CMemory::new()
            .store_union(
                base.clone(),
                CType::UInt8,
                CValue::UInt8(Bitvector32Term::Constant(0xAA)),
            )
            .store_union(
                base.clone(),
                CType::Int32,
                CValue::Int32(Bitvector32Term::Constant(0x51)),
            );
        assert_eq!(
            memory.known_union_value(&base, CType::UInt8),
            None,
            "the old byte view must not survive the wider member write"
        );
        assert_eq!(
            memory.known_union_value(&base, CType::Int32),
            Some(CValue::Int32(Bitvector32Term::Constant(0x51))),
        );
    }
}

#[cfg(test)]
mod hunt_investigation_join_tests {
    use super::*;

    /// A join retains a tombstone if any incoming arm freed the allocation,
    /// even when another arm still lists it as potentially live. A later
    /// dereference through the alias must be rejected until the paths are
    /// distinguished.
    #[test]
    fn hunt_investigation_interface_join_erases_one_arm_deallocation() {
        let base = Pointer {
            block: PointerBlock::Heap(923_001),
            offset: PointerOffsetTerm::Constant(0),
        };
        // Arm B kept it live.
        let alive = CMemory::new()
            .with_block(base.block.clone(), 8)
            .with_heap_allocation_claim(base.clone(), 8)
            .expect("fresh allocation on arm B");
        // Arm A freed it.
        let freed = alive
            .clone()
            .free_heap_block(&base, &PureFactContext::new())
            .expect("the allocation frees on arm A");
        let arms = [&alive, &freed];
        let joined = alive
            .clone()
            .with_interface_memory_havoc_preserving_loans(
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

    fn heap_base(identity: u64) -> Pointer {
        Pointer {
            block: PointerBlock::Heap(identity),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    /// Each arm holds its allocation live under its own spelling, so the
    /// join unions two live entries.
    fn joined(p: &Pointer, q: &Pointer) -> CMemory {
        let arm_a = CMemory::new()
            .with_block(p.block.clone(), 8)
            .with_heap_allocation_claim(p.clone(), 8)
            .expect("arm A claim");
        let arm_b = CMemory::new()
            .with_block(q.block.clone(), 8)
            .with_heap_allocation_claim(q.clone(), 8)
            .expect("arm B claim");
        let arms = [&arm_a, &arm_b];
        let joined = arm_a
            .clone()
            .with_interface_memory_havoc_preserving_loans(
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

    /// `with_interface_memory_havoc_preserving_loans` keys `live_allocations`
    /// by pointer spelling, so one allocation the arms spell `p` and `q`
    /// joins as two live entries. Where `p == q` is known, a free through
    /// either spelling retires both, and the other spelling cannot be freed
    /// or reported live afterwards.
    #[test]
    fn join_of_two_spellings_of_one_allocation_frees_once() {
        let p = heap_base(924_001);
        let q = Pointer {
            block: PointerBlock::Symbolic(Variable(924_005)),
            offset: PointerOffsetTerm::Constant(0),
        };
        let assumptions = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(p.clone(), q.clone()),
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
            ConditionTerm::pointer_equal(p.clone(), q.clone()),
            ConditionTerm::Constant(false)
        );
        let assumptions = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(p, q),
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
            Err(CInvalidFree::DoubleFree)
        ));
    }
}

/// One cached value a forgetting transition is asked about
/// ([`CMemory::forget_cached_values`]).
#[derive(Clone, Copy, Debug)]
pub(super) enum CachedValue<'a> {
    /// A cell, or one slot of a run.
    Cell(&'a CValue),
    /// A typed view of union storage, keyed by the member type it records.
    UnionView(CType, &'a CValue),
}

impl<'a> CachedValue<'a> {
    pub(super) fn value(self) -> &'a CValue {
        match self {
            Self::Cell(value) | Self::UnionView(_, value) => value,
        }
    }

    /// The width of the access this value answers. A union view has no
    /// value width of its own to trust, so it stands in its key type's.
    pub(super) fn byte_width(self) -> u32 {
        match self {
            Self::Cell(value) => value.byte_width(),
            Self::UnionView(c_type, _) => c_type.byte_width(),
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
        selected: &'a [Pointer],
    },
    /// Every cached value, for a transition that may have written anywhere.
    Everywhere,
    /// The values in `candidates`' blocks, except the cells inside the key
    /// ranges `cells_kept`, which the caller has shown its rule keeps
    /// ([`CellStore::retain_candidates_outside_by`]).
    Candidates {
        candidates: &'a AliasCandidates,
        cells_kept: &'a [(Pointer, Pointer)],
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

/// Collects one dropped cell for [`CMemory::record_dropped_initialized_cells`],
/// except from inside a debug self-check that re-asks a retain predicate:
/// that would record, in a debug build only, cells a release build keeps
/// by a whole-run answer.
fn push_dropped_initialized(dropped: &mut Vec<(Pointer, u32)>, cell: (Pointer, u32)) {
    if !crate::instrumentation::in_uncharged_debug_check() {
        dropped.push(cell);
    }
}

/// The entries of automatic (`local:`) blocks in a pointer-keyed map, which
/// are one contiguous key range: `local:` blocks are `Concrete` names sharing
/// that prefix.
fn local_block_entries<'a, K: BlockKeyed, V>(
    map: &'a SnapshotMap<K, V>,
) -> impl Iterator<Item = (&'a K, &'a V)> + 'a {
    map.range(K::first_key_of(&PointerBlock::from("local:"))..)
        .take_while(|(key, _)| key.key_block().starts_with("local:"))
}

#[cfg(test)]
mod initialization_record_tests {
    use super::*;

    #[test]
    fn exact_symbolic_cell_proves_only_its_stored_bytes_initialized() {
        let pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(924_019)), 4),
        };
        let assumptions = PureFactContext::new();
        let empty = CMemory::new();
        assert!(!empty.has_initialized_bytes_under(&pointer, 8, &assumptions));
        let memory = empty.store(
            pointer.clone(),
            CValue::typed_pointer(Pointer::symbolic(Variable(924_020)), CType::Int32Pointer),
        );
        assert!(memory.has_initialized_bytes_under(&pointer, 8, &assumptions));
        assert!(!memory.has_initialized_bytes_under(&pointer, 9, &assumptions));
        assert!(!memory.has_initialized_bytes_under(&pointer.offset_by_bytes(8), 1, &assumptions,));
        let range =
            CMemoryRange::new_with_element_width(pointer.clone(), 0u32.into(), 8u32.into(), 1);
        let after = memory.clone().with_call_memory_havoc(
            Variable(924_021),
            std::slice::from_ref(&range),
            &assumptions,
            None,
        );
        assert!(after.known_value(&pointer).is_none());
        assert!(after.has_initialized_bytes_under(&pointer, 8, &assumptions));
        assert!(!after.has_initialized_bytes_under(&pointer, 9, &assumptions));
        assert!(after.matches_call_memory_havoc_result(
            &memory,
            std::slice::from_ref(&range),
            &assumptions,
            None,
        ));
    }

    #[test]
    fn forgotten_symbolic_initialized_runs_stay_compressed() {
        let pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(924_022)), 4),
        };
        let mut samples = Vec::new();
        for count in [16, 256, 4096] {
            let before = CMemory::new();
            let memory = before.clone().with_seeded_cells(
                pointer.clone(),
                4,
                CType::Int32,
                0,
                count,
                crate::kernel::intern_c_memory(before),
            );
            let (after, work) =
                crate::instrumentation::measure_deterministic_work(|| loop_havoc(memory, 924_023));
            assert!(after.known_value(&pointer).is_none());
            assert!(after.has_initialized_bytes_at(&pointer, count * 4));
            assert!(!after.has_initialized_bytes_at(&pointer, count * 4 + 1));
            samples.push(work);
        }
        assert!(
            samples.iter().all(|work| *work == samples[0]),
            "{samples:?}"
        );
    }

    fn element(block: &str, index: i64) -> Pointer {
        Pointer {
            block: PointerBlock::from(block),
            offset: PointerOffsetTerm::Constant(4 * index),
        }
    }

    fn unplaced(block: &str) -> Pointer {
        Pointer {
            block: PointerBlock::from(block),
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(924_001)), 4),
        }
    }

    fn written_pair(block: &str) -> CMemory {
        CMemory::new()
            .with_block(block, 8)
            .store(
                element(block, 0),
                CValue::Int32(Bitvector32Term::Constant(5)),
            )
            .store(
                element(block, 1),
                CValue::Int32(Bitvector32Term::Constant(5)),
            )
    }

    fn forgotten_pair(block: &str) -> CMemory {
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
        let stored = forgotten.store(unplaced(block), CValue::Int32(Bitvector32Term::Constant(7)));
        assert!(stored.has_initialized_bytes_at(&element(block, 0), 8));
    }

    #[test]
    fn loop_havoc_keeps_forgotten_automatic_bytes_initialized() {
        let block = "local:record-loop";
        let havoc = written_pair(block).with_loop_memory_havoc_preserving_loans(
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
        let first_only = CMemory::new().with_block(block, 8).store(
            element(block, 0),
            CValue::Int32(Bitvector32Term::Constant(5)),
        );
        let arms = [&forgotten, &first_only];
        let joined = forgotten
            .clone()
            .with_interface_memory_havoc_preserving_loans(
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
    fn zero_runs(block: &str, count: u32, stride: u32) -> CMemory {
        let zero = CValue::Int32(Bitvector32Term::Constant(0));
        let runs = (0..stride / 4)
            .map(|field| CConstantRun {
                offset: 4 * field,
                stride,
                count,
                value: zero.clone(),
            })
            .collect::<Vec<_>>();
        CMemory::new()
            .with_block(block, count * stride)
            .with_constant_runs(&element(block, 0), &runs)
            .expect("a fresh local block takes constant runs")
    }

    fn loop_havoc(memory: CMemory, variable: u64) -> CMemory {
        memory.with_loop_memory_havoc_preserving_loans(
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
    fn a_declared_object_makes_dropping_its_runs_one_query() {
        // With the declaration's object recorded, a havoc dropping its runs
        // costs the runs, not their slots, whatever the struct count.
        let mut works = Vec::new();
        for count in [1_000u32, 10_000, 100_000] {
            let block = format!("local:record-declared-{count}");
            let memory =
                zero_runs(&block, count, 8).with_initialized_object(&element(&block, 0), count * 8);
            let (havoc, work) =
                crate::instrumentation::measure_deterministic_work(|| loop_havoc(memory, 924_006));
            assert!(havoc.has_initialized_bytes_at(&element(&block, 0), count * 8));
            works.push(work);
        }
        assert!(
            works.windows(2).all(|pair| pair[0] == pair[1]),
            "dropping declared runs cost {works:?} work units"
        );
    }

    #[test]
    fn an_ended_lifetime_forgets_its_initialization() {
        let block = "local:record-lifetime";
        let forgotten = forgotten_pair(block);
        assert!(forgotten.has_initialized_bytes_at(&element(block, 0), 4));
        let ended = forgotten.without_local_block(&PointerBlock::from(block));
        assert!(!ended.has_initialized_bytes_at(&element(block, 0), 4));
    }

    #[test]
    fn an_element_index_the_facts_bound_reads_a_covering_run() {
        let block = "local:record-index";
        let forgotten = forgotten_pair(block);
        let index = Bitvector32Term::Variable(Variable(924_004));
        let read = Pointer {
            block: PointerBlock::from(block),
            offset: PointerOffsetTerm::scale_int32(index.clone(), 4),
        };
        let bounded = |high: u32| {
            PureFactContext::new()
                .assume_condition(
                    ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone()),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_less_equal(
                        index.clone(),
                        Bitvector32Term::Constant(high),
                    ),
                    true,
                )
        };
        assert!(forgotten.has_initialized_bytes_under(&read, 4, &bounded(1)));
        assert!(!forgotten.has_initialized_bytes_under(&read, 4, &bounded(2)));
        assert!(!forgotten.has_initialized_bytes_under(&read, 4, &PureFactContext::new()));
    }

    fn index_between(index: &Bitvector32Term, low: u32, high: u32) -> PureFactContext {
        PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(low), index.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(index.clone(), Bitvector32Term::Constant(high)),
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
        let index = Bitvector32Term::Variable(Variable(924_007));
        let read = Pointer {
            block: PointerBlock::from(block),
            offset: PointerOffsetTerm::scale_int32(index.clone(), 4),
        };
        assert!(written.has_initialized_bytes_under(&read, 4, &index_between(&index, 0, 1)));
        assert!(!written.has_initialized_bytes_under(&read, 4, &index_between(&index, 0, 2)));
        let gap = CMemory::new()
            .with_block(block, 12)
            .store(
                element(block, 0),
                CValue::Int32(Bitvector32Term::Constant(5)),
            )
            .store(
                element(block, 2),
                CValue::Int32(Bitvector32Term::Constant(5)),
            );
        assert!(!gap.has_initialized_bytes_under(&read, 4, &index_between(&index, 0, 2)));
        assert!(gap.has_initialized_bytes_under(&read, 4, &index_between(&index, 2, 2)));
    }

    #[test]
    fn a_covering_query_scales_with_the_cells_it_crosses() {
        // A read bounded to two elements of an array whose every element is
        // a cached cell costs those two cells, whatever the array's size.
        let mut works = Vec::new();
        for count in [64i64, 512, 4096] {
            let block = format!("local:record-cells-{count}");
            let mut memory =
                CMemory::new().with_block(block.as_str(), u32::try_from(4 * count).unwrap());
            for index in 0..count {
                memory = memory.store(
                    element(&block, index),
                    CValue::Int32(Bitvector32Term::Constant(1)),
                );
            }
            let index = Bitvector32Term::Variable(Variable(924_008));
            let read = Pointer {
                block: PointerBlock::from(block.as_str()),
                offset: PointerOffsetTerm::scale_int32(index.clone(), 4),
            };
            let assumptions = index_between(&index, 7, 8);
            let (covered, work) = crate::instrumentation::measure_deterministic_work(|| {
                memory.has_initialized_bytes_under(&read, 4, &assumptions)
            });
            assert!(covered);
            works.push(work);
        }
        assert!(
            works.windows(2).all(|pair| pair[0] == pair[1]),
            "covering queries cost {works:?} work units"
        );
    }
}

#[cfg(test)]
mod local_variable_spelling_tests {
    use super::*;

    fn scalar(state: CState, name: &str, value: CValue) -> CState {
        let memory = state
            .memory()
            .clone()
            .store(CMemory::local_pointer(name), value.clone());
        state.with_local(name, value).with_memory(memory)
    }

    #[test]
    fn local_variable_spelling_uses_current_memory_and_stable_slot_order() {
        let variable = Variable(971_010);
        let value = CValue::UInt64(Bitvector32Term::Variable(variable));
        let state = scalar(scalar(CState::new(), "z", value.clone()), "a", value);
        assert_eq!(
            state.local_name_holding_bitvector_variable(variable),
            Some("a")
        );
        let pointer = CMemory::local_pointer("a");
        assert_eq!(
            state.local_name_holding_bitvector_variable_at(variable, &pointer),
            Some("a")
        );
        let state = state.clone().with_memory(state.memory().clone().store(
            CMemory::local_pointer("a"),
            CValue::UInt64(Bitvector32Term::UInt64Constant(0)),
        ));
        assert_eq!(
            state.local_name_holding_bitvector_variable(variable),
            Some("z")
        );
        assert_eq!(
            state.local_name_holding_bitvector_variable_at(variable, &pointer),
            None,
            "a recorded address must still hold the atom in current memory"
        );
        let state = state.clone().with_memory(state.memory().clone().store(
            CMemory::local_pointer("z"),
            CValue::UInt64(Bitvector32Term::UInt64Constant(0)),
        ));
        assert_eq!(state.local_name_holding_bitvector_variable(variable), None);
    }

    #[test]
    fn local_variable_spelling_work_is_linear_in_declared_slots() {
        for size in [4usize, 16, 64, 256, 1024] {
            let state = (0..size).fold(CState::new(), |state, index| {
                scalar(
                    state,
                    &format!("noise_{index:04}"),
                    CValue::Int32(Bitvector32Term::Constant(0)),
                )
            });
            let (name, work) = crate::instrumentation::measure_deterministic_work(|| {
                state.local_name_holding_bitvector_variable(Variable(971_011))
            });
            assert_eq!(name, None);
            assert!(
                work >= size && work <= 3 * size,
                "size {size}: {work} work must scale with inspected slots"
            );
        }
    }

    #[test]
    fn local_variable_spelling_does_not_traverse_unrelated_symbolic_values_or_heap_runs() {
        let variable = Variable(971_012);
        for depth in [4usize, 16, 64, 256, 1024] {
            let nested = (0..depth).fold(Bitvector32Term::Variable(variable), |term, _| {
                Bitvector32Term::Add(Box::new(Bitvector32Term::Constant(0)), Box::new(term))
            });
            let state = scalar(CState::new(), "noise", CValue::Int32(nested));
            let base = Pointer {
                block: "unrelated-heap".into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            let memory = state.memory().clone().with_seeded_cells(
                base,
                4,
                CType::Int32,
                0,
                1_000_000,
                CMemory::new().into(),
            );
            let state = state.with_memory(memory);
            let (name, work) = crate::instrumentation::measure_deterministic_work(|| {
                state.local_name_holding_bitvector_variable(variable)
            });
            assert_eq!(
                name, None,
                "a variable inside an expression is not the held scalar atom"
            );
            assert_eq!(
                work, 2,
                "depth {depth}: only the slot inspection and budget check participate"
            );
        }
    }
}

#[cfg(test)]
mod declared_domain_producer_tests {
    use super::*;

    fn address(name: &str) -> Pointer {
        Pointer {
            block: name.into(),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    #[test]
    fn native_callback_member_address_keeps_the_declared_typed_access() {
        use crate::kernel::eval::pointer_domains::{PointerDomainView, checked_pointer_access};
        let _session = crate::kernel::VerificationSession::enter();
        let signature = CType::function_pointer_signature(CType::Void, &[CType::Int32Pointer]);
        let field_type = CType::FunctionPointer(signature);
        let layout = Arc::new(CAggregateLayout::new(
            8,
            8,
            vec![CAggregateField::new("callback", 0, field_type)],
        ));
        let input = Variable(987_340);
        let owner = CPointerValue::new(Pointer::symbolic(input), CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(input));
        let memory = CMemory::new()
            .with_native_record_input(owner.clone(), layout.clone())
            .unwrap();
        let selection = CAggregateMemberSelection {
            layout,
            path: vec!["callback".into()].into(),
            value_type: field_type,
        };
        let facts = PureFactContext::new();
        let (selected, _) = memory
            .guarded_native_record_selection(&owner, &selection, &facts)
            .unwrap();
        assert_eq!(selected.c_type(), CType::Int32Pointer);
        let state = CState::new().with_memory(memory);
        assert!(
            checked_pointer_access(
                &state,
                &selected,
                field_type,
                C_POINTER_BYTE_WIDTH,
                PointerDomainView::Typed,
                &facts
            )
            .is_ok()
        );
        let incompatible = CType::FunctionPointer(CType::function_pointer_signature(
            CType::Int32,
            &[CType::Int32Pointer],
        ));
        assert!(
            checked_pointer_access(
                &state,
                &selected,
                incompatible,
                C_POINTER_BYTE_WIDTH,
                PointerDomainView::Typed,
                &facts
            )
            .is_err()
        );
        assert!(
            checked_pointer_access(
                &state,
                &selected,
                field_type,
                C_POINTER_BYTE_WIDTH,
                PointerDomainView::ObjectRepresentationBytes,
                &facts
            )
            .is_err()
        );
    }

    #[test]
    fn array_domains_require_the_actual_declaration_and_preserve_the_extent() {
        let root = address("local:array-domain");
        let declared = CMemory::new()
            .with_declared_array_block(root.block.clone(), CType::Int32, 4)
            .unwrap();
        let pointer = declared
            .declared_array_pointer(&root, CType::Int32, 4)
            .unwrap();
        assert!(declared.authenticated_pointer_domain_at_base(&pointer));
        assert!(declared.authenticated_pointer_domain_at_base(
            &pointer.clone().with_pointer(root.offset_by_bytes(16))
        ));
        assert!(
            declared
                .declared_array_pointer(&root, CType::Int32, 3)
                .is_none()
        );
        assert!(
            declared
                .declared_array_pointer(&root, CType::UInt32, 4)
                .is_none()
        );
        assert!(
            !CMemory::new()
                .with_block(root.block.clone(), 16)
                .authenticated_pointer_domain_at_base(&pointer)
        );
        assert!(
            !declared.authenticated_pointer_domain_at_base(&CPointerValue::new(
                root.clone(),
                CType::Int32Pointer
            ))
        );
        assert_eq!(declared.cells.representation_len(), 0);
        assert!(!declared.has_initialized_bytes_under(&root, 16, &PureFactContext::new()));
        let written = declared
            .clone()
            .store(root.clone(), CValue::Int32(7u32.into()));
        let havoc = written.clone().with_storage_memory_havoc(
            Variable(9_901_000),
            &[CMemoryRange::new_with_element_width(
                root.clone(),
                0u32.into(),
                4u32.into(),
                4,
            )],
            &PureFactContext::new(),
        );
        let joined = written
            .clone()
            .with_interface_memory_havoc(
                Variable(9_901_001),
                &BTreeSet::new(),
                &[&written, &declared],
            )
            .unwrap();
        for memory in [&written, &havoc, &joined] {
            assert!(memory.authenticated_pointer_domain_at_base(&pointer));
        }
        let conflicting = CMemory::new()
            .with_declared_array_block(root.block.clone(), CType::UInt32, 4)
            .unwrap();
        assert!(
            written
                .with_interface_memory_havoc(
                    Variable(9_901_002),
                    &BTreeSet::new(),
                    &[&declared, &conflicting]
                )
                .is_err()
        );
        assert!(
            !declared
                .without_local_block(&root.block)
                .authenticated_pointer_domain_at_base(&pointer)
        );
        assert!(
            CMemory::new()
                .with_declared_array_block(root.block.clone(), CType::Int32, u32::MAX)
                .is_none()
        );
        assert!(
            CMemory::new()
                .with_declared_array_block(root.block, CType::Void, 1)
                .is_none()
        );
    }

    #[test]
    fn structural_record_declarations_do_not_supply_cpp_nominal_identity_or_padding() {
        let root = address("local:structural-record");
        let layout =
            CAggregateLayout::new(8, 4, vec![CAggregateField::new("first", 0, CType::Int32)]);
        let declared = CMemory::new().with_declared_aggregate_block(root.block.clone(), &layout);
        let pointer = declared.declared_aggregate_pointer(&root, &layout).unwrap();
        assert!(declared.authenticated_pointer_domain_at_base(&pointer));
        assert!(declared.has_aggregate_object_domain(&pointer, &layout));
        let native = layout.clone().with_declaration_identity(Some(Arc::new(
            CppRecordDeclarationIdentity::new("domain-producer-test", "Record"),
        )));
        assert!(!declared.has_aggregate_object_domain(&pointer, &native));
        let native_declared =
            CMemory::new().with_declared_aggregate_block(root.block.clone(), &native);
        let native_pointer = native_declared
            .declared_aggregate_pointer(&root, &native)
            .unwrap();
        assert!(native_declared.has_aggregate_object_domain(&native_pointer, &native));
        assert!(!native_declared.has_aggregate_object_domain(&native_pointer, &layout));
        assert!(!declared.has_initialized_bytes_under(
            &root.offset_by_bytes(4),
            4,
            &PureFactContext::new()
        ));
        assert_eq!(declared.cells.representation_len(), 0);
    }

    #[test]
    fn target_representation_and_scalar_authority_policy_are_declaration_metadata() {
        let root = address("local:uint32-profile");
        let targeted = CMemory::new().with_declared_scalar_block_in_target(
            root.block.clone(),
            4,
            CType::UInt32,
            Some(ByteOrder::Little),
        );
        assert_eq!(
            targeted.declared_uint32_representation(&root),
            Some(UInt32RepresentationProfile::LittleEndian)
        );
        assert!(targeted.requires_explicit_scalar_ownership(&root));
        assert!(!targeted.has_initialized_bytes_under(&root, 4, &PureFactContext::new()));
        for memory in [
            CMemory::new().with_declared_scalar_block(root.block.clone(), 4, CType::UInt32),
            CMemory::new().with_declared_scalar_block_in_target(
                root.block.clone(),
                4,
                CType::UInt32,
                Some(ByteOrder::Big),
            ),
            CMemory::new().with_declared_scalar_block_in_target(
                root.block.clone(),
                4,
                CType::Int32,
                Some(ByteOrder::Little),
            ),
            CMemory::new()
                .with_block(root.block.clone(), 4)
                .store(root.clone(), CValue::UInt32(0u32.into())),
        ] {
            assert_eq!(memory.declared_uint32_representation(&root), None);
        }
        assert_eq!(
            targeted.declared_uint32_representation(&root.offset_by_bytes(1)),
            None
        );
        assert_eq!(
            targeted
                .without_local_block(&root.block)
                .declared_uint32_representation(&root),
            None
        );
        let global = CMemory::new().with_declared_scalar_block_or_read_only(
            root.block.clone(),
            4,
            CType::UInt32,
            true,
        );
        assert!(!global.requires_explicit_scalar_ownership(&root));
        assert!(global.blocks.get(&root.block).unwrap().is_read_only());
    }

    #[test]
    fn selected_array_domain_authentication_ignores_unrelated_declarations() {
        let mut samples = Vec::new();
        for count in [16, 128, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let root = address("local:selected-array");
            let mut memory = CMemory::new()
                .with_declared_array_block(root.block.clone(), CType::Int32, 4)
                .unwrap();
            for i in 0..count {
                memory = memory
                    .with_declared_array_block(
                        format!("local:unrelated-array-{i}").into(),
                        CType::UInt8,
                        16,
                    )
                    .unwrap();
            }
            let pointer = memory
                .declared_array_pointer(&root, CType::Int32, 4)
                .unwrap();
            let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
                memory.authenticated_pointer_domain_at_base(&pointer)
            });
            assert!(checked);
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[0] == pair[1]),
            "array authentication scanned unrelated declarations: {samples:?}"
        );
    }
}

#[cfg(test)]
mod scalar_array_layout_tests {
    use super::*;

    #[test]
    fn explicit_array_layouts_are_checked_and_distinct_from_empty_records() {
        let _session = crate::kernel::VerificationSession::enter();
        let array = CAggregateLayout::new_scalar_array(CType::UInt32, 2).unwrap();
        let record = CAggregateLayout::new(8, 4, Vec::new());
        assert_eq!(array.scalar_array(), Some((CType::UInt32, 2)));
        assert_ne!(array, record);
        assert!(!array.selects_layout_path(&[], &record));
        assert!(!record.selects_layout_path(&[], &array));
        assert!(array.selects_layout_path(&[], &array.clone()));
        assert!(!array.selects_layout_path(&[], &record));
        let hash = |layout: &CAggregateLayout| {
            let mut state = std::collections::hash_map::DefaultHasher::new();
            std::hash::Hash::hash(layout, &mut state);
            std::hash::Hasher::finish(&state)
        };
        assert_ne!(hash(&array), hash(&record));
        assert!(CAggregateLayout::new_scalar_array(CType::UInt32, u32::MAX).is_none());
        assert!(CAggregateLayout::new_scalar_array(CType::Void, 2).is_none());
        assert!(CAggregateLayout::new_scalar_array(CType::UInt32Array(u32::MAX), 2).is_none());
        assert!(
            CAggregateLayout::new_scalar_array(
                CType::FunctionPointer(CallbackSignature::UNSPECIFIED),
                2
            )
            .is_none()
        );
        assert!(
            CAggregateLayout::new_scalar_array_with_fields(
                CType::UInt32,
                2,
                vec![
                    CAggregateField::new("0", 0, CType::UInt32),
                    CAggregateField::new("1", 4, CType::UInt32),
                ]
            )
            .is_some()
        );
        assert!(
            CAggregateLayout::new_scalar_array_with_fields(
                CType::UInt32,
                2,
                vec![
                    CAggregateField::new("0", 0, CType::UInt32),
                    CAggregateField::new("1", 4, CType::Int32),
                ]
            )
            .is_none()
        );
        assert!(
            CAggregateLayout::new_scalar_array_with_fields(
                CType::UInt32,
                2,
                vec![
                    CAggregateField::new("0", 0, CType::UInt32),
                    CAggregateField::new("1", 0, CType::UInt32),
                ]
            )
            .is_none()
        );
        let address = CMemory::frame_local_pointer(949_050, "array");
        let declared = CMemory::new().with_declared_aggregate_block(address.block.clone(), &array);
        let legacy = CMemory::new().with_declared_aggregate_block(address.block.clone(), &record);
        assert!(
            declared
                .clone()
                .with_interface_memory_havoc(
                    Variable(949_052),
                    &BTreeSet::new(),
                    &[&declared, &legacy]
                )
                .is_err()
        );
    }

    #[test]
    fn explicit_array_aggregate_declarations_issue_only_the_actual_array_domain() {
        let _session = crate::kernel::VerificationSession::enter();
        let layout = CAggregateLayout::new_scalar_array(CType::UInt32, 2).unwrap();
        let address = CMemory::frame_local_pointer(949_051, "array");
        let memory = CMemory::new().with_declared_aggregate_block(address.block.clone(), &layout);
        let pointer = memory
            .declared_aggregate_pointer(&address, &layout)
            .unwrap();
        assert!(memory.has_declared_array_domain(&pointer));
        assert!(memory.has_aggregate_object_domain(&pointer, &layout));
        assert!(memory.authenticated_pointer_domain_at_base(
            &pointer.clone().with_pointer(address.offset_by_bytes(4))
        ));
        let Some(PointerDesignation::Object {
            element_type,
            stride,
            count,
            ..
        }) = pointer.designation()
        else {
            panic!()
        };
        assert_eq!(*element_type, CType::UInt32);
        assert_eq!(*stride, 4);
        assert_eq!(
            *count,
            SharedIntegerTerm::from(IntegerTerm::constant_i64(2))
        );
        assert!(
            memory
                .declared_array_pointer(&address, CType::UInt32, 3)
                .is_none()
        );
        let legacy = CAggregateLayout::new(8, 4, Vec::new());
        let fake_record =
            CMemory::aggregate_input_pointer(address.clone(), &legacy, CType::UInt8Pointer);
        assert!(!memory.authenticated_pointer_domain_at_base(&fake_record));
        assert!(
            memory
                .declared_aggregate_pointer(&address, &legacy)
                .is_none()
        );
        assert_eq!(memory.cells.representation_len(), 0);
        assert!(!memory.has_initialized_bytes_under(&address, 8, &PureFactContext::new()));
        let updated = memory
            .clone()
            .store(address.clone(), CValue::UInt32(9u32.into()));
        assert!(updated.has_declared_array_domain(&pointer));
        assert!(
            !memory
                .without_local_block(&address.block)
                .authenticated_pointer_domain_at_base(&pointer)
        );
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            CAggregateLayout::new_scalar_array(CType::UInt32, 1_000_000).unwrap()
        });
        assert!(
            work <= 1,
            "compact array metadata expanded elements: {work}"
        );
    }
}

#[cfg(test)]
mod allocated_scalar_producer_tests {
    use super::*;

    fn pending(identity: Variable, zeroed: bool) -> (CMemory, CPointerValue) {
        let pointer = CPointerValue::new(Pointer::symbolic(identity), CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(identity));
        let memory = CMemory::new()
            .with_pending_allocated_scalar(
                pointer.pointer().clone(),
                8u32.into(),
                zeroed,
                CType::Int32,
                identity,
            )
            .unwrap();
        (memory, pointer)
    }

    #[test]
    fn matching_literal_prefixes_merge_without_granting_hole_permissions_or_initialization() {
        let _session = crate::kernel::VerificationSession::enter();
        let identity = Variable(989_714);
        let pointer = CPointerValue::new(Pointer::symbolic(identity), CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(identity));
        let policy = CTypedAccessPolicy::CAllocatedAccessAllowed;
        let memory = CMemory::new()
            .with_typed_input_span(
                pointer.clone(),
                CType::Int32,
                IntegerTerm::constant_i64(1).into(),
                policy,
            )
            .unwrap()
            .with_typed_input_span(
                pointer.clone(),
                CType::Int32,
                IntegerTerm::constant_i64(2).into(),
                policy,
            )
            .unwrap()
            .with_typed_input_span(
                pointer.clone(),
                CType::Int32,
                IntegerTerm::constant_i64(5).into(),
                policy,
            )
            .unwrap()
            .with_typed_input_span(
                pointer.clone(),
                CType::Int32,
                IntegerTerm::constant_i64(1).into(),
                policy,
            )
            .unwrap();
        let (_, element, count) = memory.native_input_span(&pointer).unwrap();
        assert_eq!(element, CType::Int32);
        assert_eq!(count, IntegerTerm::constant_i64(5).into());
        assert!(!memory.has_initialized_bytes_under(pointer.pointer(), 4, &PureFactContext::new()));
        let resources = ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
            CMemoryRange::new(pointer.pointer().clone(), 4u32.into(), 5u32.into()),
        ));
        assert!(!resources.satisfies_fact(
            &CResourceFact::own_memory(CMemoryRange::new(
                pointer.pointer().clone(),
                0u32.into(),
                1u32.into()
            ),),
            &PureFactContext::new()
        ));
        assert!(
            memory
                .clone()
                .with_typed_input_span(
                    pointer.clone(),
                    CType::Int32,
                    IntegerTerm::constant_i64(6).into(),
                    CTypedAccessPolicy::NativeObjectOnly
                )
                .is_err()
        );
        assert!(
            memory
                .with_typed_input_span(
                    pointer,
                    CType::UInt32,
                    IntegerTerm::constant_i64(6).into(),
                    policy
                )
                .is_err()
        );
    }

    #[test]
    fn allocated_scalar_witness_requires_actual_success_and_exact_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let (pending, pointer) = pending(Variable(989_710), false);
        assert!(pending.allocated_scalar_extent(&pointer).is_none());
        assert!(
            pending
                .resolved_allocated_scalar_pointer(pointer.pointer())
                .is_none()
        );
        let pending_base = pointer.pointer().clone();
        let (failed, _, _) = pending
            .clone()
            .resolve_pending_heap_allocation(pointer.pointer(), false)
            .unwrap();
        assert!(failed.allocated_scalar_extent(&pointer).is_none());
        let (memory, _, base) = pending
            .resolve_pending_heap_allocation(pointer.pointer(), true)
            .unwrap();
        let pointer = pointer.with_pointer(base.clone());
        let (origin, element, bytes) = memory.allocated_scalar_extent(&pointer).unwrap();
        assert_eq!(origin, pointer);
        assert_eq!(
            memory.resolved_allocated_scalar_pointer(&pending_base),
            Some(pointer.clone())
        );
        assert_eq!(element, CType::Int32);
        assert_eq!(bytes, IntegerTerm::constant_i64(8).into());
        assert!(!memory.has_initialized_bytes_under(&base, 4, &PureFactContext::new()));
        assert!(
            memory
                .allocated_scalar_extent(&CPointerValue::new(base.clone(), CType::Int32Pointer))
                .is_none()
        );
        assert!(
            memory
                .allocated_scalar_extent(
                    &pointer
                        .clone()
                        .with_designation(PointerDesignation::Unresolved(Variable(989_711)))
                )
                .is_none()
        );
        let claimed = CMemory::new()
            .with_heap_allocation_claim(base.clone(), 8)
            .unwrap();
        assert!(claimed.allocated_scalar_extent(&pointer).is_none());
        let retired = memory
            .free_heap_block(&base, &PureFactContext::new())
            .unwrap();
        assert!(retired.allocated_scalar_extent(&pointer).is_none());
    }

    #[test]
    fn scalar_reallocation_success_transfers_profile_and_failure_preserves_old() {
        let _session = crate::kernel::VerificationSession::enter();
        let (memory, pointer) = pending(Variable(989_712), false);
        let (memory, _, base) = memory
            .resolve_pending_heap_allocation(pointer.pointer(), true)
            .unwrap();
        let old = pointer.with_pointer(base.clone());
        let memory = memory.store(base, int32(42));
        let new_identity = Variable(989_713);
        let new_base = Pointer::symbolic(new_identity);
        let pending = memory
            .with_pending_allocated_scalar(
                new_base.clone(),
                12u32.into(),
                false,
                CType::Int32,
                new_identity,
            )
            .unwrap()
            .with_pending_heap_reallocation(
                new_base.clone(),
                old.clone(),
                8u32.into(),
                None,
                vec![(PointerOffsetTerm::Constant(0), int32(42))],
                vec![(0, 4)],
            );
        let new_pointer = CPointerValue::new(new_base.clone(), CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(new_identity));
        let (failure, _, _, _) = pending
            .clone()
            .resolve_pending_heap_reallocation(&new_base, false, &PureFactContext::new())
            .unwrap();
        assert!(failure.allocated_scalar_extent(&old).is_some());
        assert!(failure.allocated_scalar_extent(&new_pointer).is_none());
        let (success, _, resolved, _) = pending
            .resolve_pending_heap_reallocation(&new_base, true, &PureFactContext::new())
            .unwrap();
        assert!(success.allocated_scalar_extent(&old).is_none());
        let (_, element, bytes) = success
            .allocated_scalar_extent(&new_pointer.with_pointer(resolved.clone()))
            .unwrap();
        assert_eq!(element, CType::Int32);
        assert_eq!(bytes, IntegerTerm::constant_i64(12).into());
        assert!(success.has_initialized_bytes_under(&resolved, 4, &PureFactContext::new()));
        assert!(!success.has_initialized_bytes_under(
            &resolved.offset_by_bytes(8),
            4,
            &PureFactContext::new()
        ));
    }
}
