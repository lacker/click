use super::*;
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
    let mut identity = String::from("range(");
    let mut tasks = vec![
        HavocIdentityTask::Text(")"),
        HavocIdentityTask::Bitvector(Bitvector32Term::Constant(range.element_width())),
        HavocIdentityTask::Text(","),
        HavocIdentityTask::Bitvector(range.end().clone()),
        HavocIdentityTask::Text(","),
        HavocIdentityTask::Bitvector(range.start().clone()),
        HavocIdentityTask::Text(","),
        HavocIdentityTask::Pointer(range.base().clone()),
    ];
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
                    Bitvector32Term::MemoryLoad(_, pointer) => {
                        identity.push_str("load(");
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
                    ConditionTerm::IntegerLessThan(_, _)
                    | ConditionTerm::IntegerLessEqual(_, _)
                    | ConditionTerm::IntegerGreaterThan(_, _)
                    | ConditionTerm::IntegerGreaterEqual(_, _)
                    | ConditionTerm::IntegerEqual(_, _)
                    | ConditionTerm::IntegerNotEqual(_, _) => {
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
        );
        let second = before.clone().with_call_memory_havoc(
            Variable(95_000),
            std::slice::from_ref(&second_range),
            &PureFactContext::new(),
        );
        assert_ne!(
            first, second,
            "distinct deep write sets need distinct endpoints"
        );
        assert!(first.matches_call_memory_havoc_result(
            &before,
            std::slice::from_ref(&first_range),
            &PureFactContext::new(),
        ));
        assert!(!first.matches_call_memory_havoc_result(
            &before,
            std::slice::from_ref(&second_range),
            &PureFactContext::new(),
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
                range.start().as_const(),
                range.end().as_const(),
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
/// A resource range counts its own elements while a loadability fact counts
/// bytes, so the two meet at the held range's element width: reading the fact's
/// extent back through [`element_count_from_bytes`] at that width inverts the
/// scaling [`memory_range_byte_count`] applied when the clause was lowered, and
/// the required range is then in the same coordinate system as the held one.
///
/// The width has to come from the *range*, not from the shape of the extent
/// term. `memory_range_byte_count` folds a factor of one away, so a `uint8[]`
/// clause `s[0..n]` arrives here as the bare count `n` rather than `n * 1`;
/// asking the term which width it was scaled by cannot tell that apart from a
/// byte count that is no element range at all, and a byte buffer would never be
/// recognised. Two-byte and wider ranges keep their explicit product and are
/// read back exactly as before.
///
/// Width one weakens nothing. [`element_count_from_bytes`] at width one is the
/// identity, so the required range names exactly the bytes the fact names: no
/// product is formed, so none can wrap, and a byte count simply *is* its own
/// element count. The nonnegativity half of the valid-extent condition still
/// matters and is still asked — it is the held clause's own obligation,
/// discharged where the clause was stated — and `memory_range_covers` still has
/// to place the required range inside the held one.
pub(crate) fn resource_context_has_symbolic_range_read(
    resources: &ResourceContext,
    base: &Pointer,
    bytes: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    resources.facts().iter().any(|fact| {
        let Some(range) = fact.memory_range() else {
            return false;
        };
        let element_width = range.element_width();
        let Some(elements) =
            crate::kernel::reasoning::element_count_from_bytes(bytes, element_width)
        else {
            return false;
        };
        let required = CMemoryRange::new_with_element_width(
            base.clone(),
            Bitvector32Term::Constant(0),
            elements,
            element_width,
        );
        crate::kernel::primitives::resource_algebra::memory_range_covers(
            range,
            &required,
            assumptions,
        )
    })
}

impl CLocalEnvironment {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with(mut self, name: impl Into<String>, value: CValue) -> Self {
        self.set(name, value);
        self
    }

    pub fn with_typed(mut self, name: impl Into<String>, value: CValue, c_type: CType) -> Self {
        self.set_typed(name, value, c_type);
        self
    }

    pub fn with_int32_array(mut self, name: impl Into<String>, length: u32) -> Self {
        self.set_int32_array(name, length);
        self
    }

    pub fn set(&mut self, name: impl Into<String>, value: CValue) {
        let c_type = value.c_type();
        self.set_typed(name, value, c_type);
    }

    pub fn set_typed(&mut self, name: impl Into<String>, value: CValue, c_type: CType) {
        self.set_typed_with_qualifiers(name, value, c_type, false, false);
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
        self.insert_binding(
            name.into(),
            CLocalBinding::Object {
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

    pub fn set_int32_array(&mut self, name: impl Into<String>, length: u32) {
        self.set_array_object(name, CType::Int32, length);
    }

    pub fn set_uint8_array(&mut self, name: impl Into<String>, length: u32) {
        self.set_array_object(name, CType::UInt8, length);
    }

    pub fn set_int8_array(&mut self, name: impl Into<String>, length: u32) {
        self.set_array_object(name, CType::Int8, length);
    }

    pub fn set_int16_array(&mut self, name: impl Into<String>, length: u32) {
        self.set_array_object(name, CType::Int16, length);
    }

    pub fn set_uint16_array(&mut self, name: impl Into<String>, length: u32) {
        self.set_array_object(name, CType::UInt16, length);
    }

    pub fn set_uint32_array(&mut self, name: impl Into<String>, length: u32) {
        self.set_array_object(name, CType::UInt32, length);
    }

    pub fn set_int64_array(&mut self, name: impl Into<String>, length: u32) {
        self.set_array_object(name, CType::Int64, length);
    }

    pub fn set_uint64_array(&mut self, name: impl Into<String>, length: u32) {
        self.set_array_object(name, CType::UInt64, length);
    }

    pub(in crate::kernel) fn set_array_object(
        &mut self,
        name: impl Into<String>,
        element_type: CType,
        length: u32,
    ) {
        let name = name.into();
        self.set_array_object_at(
            name.clone(),
            element_type,
            length,
            CMemory::local_pointer(&name),
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

    pub(in crate::kernel) fn scalar_object_type(&self, name: &str) -> Option<CType> {
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
        }
    }

    pub fn read_only(size: u32) -> Self {
        Self {
            size: Bitvector32Term::Constant(size),
            read_only: true,
        }
    }

    pub(in crate::kernel) fn with_symbolic_size(size: Bitvector32Term) -> Self {
        Self {
            size,
            read_only: false,
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
/// The `local:` disjunct is the `local_versus_argument` arm of
/// [`PointerBlock::proven_distinct`] spelled as a prefix: a `local:` block is
/// storage this function declared, and memory a callee reaches through its
/// arguments existed before the call. It is only sound while a checked write
/// set can never be based in a `local:` block, which holds because such a
/// write set is the callee's owned ranges resolved at the call site, and a
/// `local:` range cannot be owned — passing `&t` to a callee that owns
/// `t[0..1]` is refused for want of `owns local:t@0[0..1]`.
fn call_havoc_keeps_cell(
    pointer: &Pointer,
    mutable_ranges: &[CMemoryRange],
    assumptions: &PureFactContext,
) -> bool {
    pointer.block.starts_with("local:")
        || assumptions.ranges_proven_disjoint_from_pointer(mutable_ranges, pointer)
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
    value: &CValue,
    union_widths: &BTreeMap<Pointer, u32>,
    preserved_blocks: &BTreeSet<PointerBlock>,
    ledger: Option<&crate::kernel::loans::LoanLedger>,
) -> bool {
    let byte_width = value
        .byte_width()
        .max(union_widths.get(pointer).copied().unwrap_or(0));
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
            std::sync::Arc::make_mut(&mut self.blocks).insert(block, CBlock::new(size));
            return self;
        }
        let base = intern_c_memory_ref(&self);
        std::sync::Arc::make_mut(&mut self.blocks).insert(block.clone(), CBlock::new(size));
        record_c_memory_derivation(&self, CMemoryDerivation::BlockDeclared { base, block });
        self
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
        let base = intern_c_memory_ref(&self);
        std::sync::Arc::make_mut(&mut self.blocks).insert(block.clone(), CBlock::read_only(size));
        record_c_memory_derivation(&self, CMemoryDerivation::BlockDeclared { base, block });
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
        std::sync::Arc::make_mut(&mut self.blocks).insert(block.into(), CBlock::new(size));
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
        let base = intern_c_memory_ref(&memory);
        std::sync::Arc::make_mut(&mut memory.blocks).remove(block);
        // Only the retired block's own cells go: one key range each.
        let own = AliasCandidates::only_block(block);
        own.retain_map(std::sync::Arc::make_mut(&mut memory.cells), |_, _| false);
        own.retain_map(std::sync::Arc::make_mut(&mut memory.union_cells), |_, _| {
            false
        });
        std::sync::Arc::make_mut(&mut memory.forgotten)
            .ended_local_blocks
            .insert(block.clone());
        record_c_memory_derivation(
            &memory,
            CMemoryDerivation::LocalLifetimeEnded {
                base,
                block: block.clone(),
            },
        );
        memory
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
        let base = Some(intern_c_memory_ref(&self));
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
        candidates.retain_map(&mut heap.initialized_cells, |cell, _| !freed_within(cell));
        candidates.retain_map(std::sync::Arc::make_mut(&mut self.cells), |cell, _| {
            !aliased_blocks.contains(&cell.block) && !freed_within(cell)
        });
        if let Some(base) = base {
            record_c_memory_derivation(
                &self,
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

    pub(in crate::kernel) fn is_zeroed_heap_address(
        &self,
        pointer: &Pointer,
        byte_width: u32,
        assumptions: &PureFactContext,
    ) -> bool {
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
                let prior = Some(intern_c_memory_ref(&self));
                std::sync::Arc::make_mut(&mut self.heap)
                    .live_allocations
                    .insert(base, bytes);
                if let Some(prior) = prior {
                    record_c_memory_derivation(
                        &self,
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
        let prior = intern_c_memory_ref(&self);
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
        candidates.retain_map(&mut heap.initialized_cells, |candidate, _| {
            !retired_cell(candidate)
        });
        candidates.retain_map(std::sync::Arc::make_mut(&mut self.cells), |candidate, _| {
            !retired_cell(candidate)
        });
        candidates.retain_map(
            std::sync::Arc::make_mut(&mut self.union_cells),
            |(candidate, _), _| !retired_cell(candidate),
        );
        for block in &retired_blocks {
            if *block != PointerBlock::ExternalArgument {
                std::sync::Arc::make_mut(&mut self.blocks).remove(block);
            }
        }
        // Losing an allocation's cached knowledge can otherwise re-intern as
        // an older empty snapshot and drop this safety-critical edge.
        self.mark_forgotten_from(&prior);
        record_c_memory_derivation(
            &self,
            CMemoryDerivation::ContractAllocationRetired {
                base: prior,
                allocation_base: base.clone(),
                bytes: bytes.clone(),
            },
        );
        self
    }

    pub(in crate::kernel) fn with_pending_heap_allocation(
        mut self,
        base: Pointer,
        bytes: Bitvector32Term,
        zeroed: bool,
    ) -> Self {
        let prior = Some(intern_c_memory_ref(&self));
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
                &self,
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
        old_pointer: Pointer,
        old_bytes: Bitvector32Term,
        zeroed_prefix: Option<Bitvector32Term>,
        copied_cells: Vec<(PointerOffsetTerm, CValue)>,
    ) -> Self {
        std::sync::Arc::make_mut(&mut self.heap)
            .pending_reallocations
            .insert(
                base,
                CPendingReallocation {
                    old_pointer,
                    old_bytes,
                    zeroed_prefix,
                    copied_cells,
                },
            );
        self
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
        let prior = Some(intern_c_memory_ref(&self));
        let bytes = std::sync::Arc::make_mut(&mut self.heap)
            .pending_allocations
            .remove(base)?;
        let zeroed = std::sync::Arc::make_mut(&mut self.heap)
            .zeroed_pending_allocations
            .remove(base);
        let resolved_base = if succeeds {
            let PointerBlock::Symbolic(Variable(identity)) = base.block else {
                return None;
            };
            Pointer {
                block: PointerBlock::Heap(identity),
                offset: PointerOffsetTerm::Constant(0),
            }
        } else {
            Pointer::null()
        };
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
                    &self,
                    CMemoryDerivation::HeapAllocated {
                        base: prior,
                        block: resolved_base.block.clone(),
                        bytes: bytes.clone(),
                    },
                );
            }
        }
        Some((self, bytes, resolved_base))
    }

    pub(in crate::kernel) fn resolve_pending_heap_reallocation(
        mut self,
        base: &Pointer,
        succeeds: bool,
        assumptions: &PureFactContext,
    ) -> Option<(Self, Bitvector32Term, Pointer, CPendingReallocation)> {
        let pending = std::sync::Arc::make_mut(&mut self.heap)
            .pending_reallocations
            .remove(base)?;
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
            for (offset, value) in &pending.copied_cells {
                memory = memory.store(
                    Pointer {
                        block: resolved_base.block.clone(),
                        offset: offset.clone(),
                    },
                    value.clone(),
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
        // pointer, any cell it can reach. Drop concrete cells outside the
        // preserved (scalar stack local) blocks so loop-head and post-loop
        // reads do not observe stale pre-loop values. A checked footprint is
        // retained on the derivation edge for disjoint-load transport; the
        // marker block still distinguishes this havoc from ordinary memory.
        let base = Some(intern_c_memory_ref(&self));
        // Whole-map by design, unlike the per-access rules that visit only
        // `AliasCandidates`: the body may write through any pointer it can
        // reach, so every cell is a candidate. The work is the cells dropped
        // plus the ones something else keeps (declared locals and
        // loan-protected bytes), charged by `retain`.
        let union_widths = union_overlay_widths(&self);
        std::sync::Arc::make_mut(&mut self.cells).retain(|pointer, value| {
            loan_preserving_havoc_keeps_cell(
                pointer,
                value,
                &union_widths,
                preserved_blocks,
                ledger,
            )
        });
        std::sync::Arc::make_mut(&mut self.blocks).insert(
            format!("havoc:{}", variable.0).into(),
            CBlock::new(mutable_ranges.map_or(0, memory_havoc_write_set_fingerprint)),
        );
        if let Some(base) = base {
            record_c_memory_derivation(
                &self,
                CMemoryDerivation::LoopHavoc {
                    base,
                    variable,
                    mutable_ranges: mutable_ranges.map(|ranges| ranges.to_vec()),
                },
            );
        }
        self
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
    /// branch may be transported across it without explicit interface facts.
    #[allow(dead_code)]
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
        let Some(first) = sibling_memories.first() else {
            return Err("an interface memory join has no sibling states".to_string());
        };

        let mut blocks = SnapshotMap::new();
        let mut ended_local_blocks = SnapshotSet::new();
        for memory in sibling_memories {
            for (block, contents) in memory.blocks.iter() {
                if let Some(existing) = blocks.insert(block.clone(), contents.clone())
                    && existing != *contents
                {
                    return Err(format!(
                        "interface arms disagree on the size of memory block {block:?}"
                    ));
                }
            }
            ended_local_blocks.extend(memory.forgotten.ended_local_blocks.iter().cloned());
        }

        let mut live_allocations = SnapshotMap::new();
        for memory in sibling_memories {
            for (base, bytes) in &memory.heap.live_allocations {
                if let Some(existing) = live_allocations.insert(base.clone(), bytes.clone())
                    && existing != *bytes
                {
                    return Err(format!(
                        "interface arms disagree on the size of heap allocation {base:?}"
                    ));
                }
            }
        }

        let mut deallocated_allocations = SnapshotMap::new();
        for memory in sibling_memories {
            for (base, bytes) in &memory.heap.deallocated_allocations {
                if let Some(existing) = deallocated_allocations.insert(base.clone(), bytes.clone())
                    && existing != *bytes
                {
                    return Err(format!(
                        "interface arms disagree on the size of freed heap allocation {base:?}"
                    ));
                }
            }
        }

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

        let mut uninitialized_allocations = first.heap.uninitialized_allocations.clone();
        for memory in sibling_memories {
            uninitialized_allocations.extend(memory.heap.uninitialized_allocations.iter().cloned());
        }

        // A scalar cell is definitely initialized at the join only when every
        // incoming arm has initialized a compatible cell at that address.
        // This metadata carries initialization, not a value, so it remains
        // useful after the join's conservative value havoc.
        let mut initialized_cells = first.heap.initialized_cells.clone();
        initialized_cells.retain(|pointer, width| {
            sibling_memories
                .iter()
                .all(|memory| memory.heap.initialized_cells.get(pointer) == Some(width))
        });

        // A zero marker is a value guarantee, so it is retained only when
        // every arm provides it. (The uninitialized marker above is instead
        // unioned because a possibly-uninitialized read must remain unsafe.)
        let mut zeroed_allocations = first.heap.zeroed_allocations.clone();
        zeroed_allocations.retain(|base| {
            sibling_memories
                .iter()
                .all(|memory| memory.heap.zeroed_allocations.contains(base))
        });
        let mut zeroed_prefix_allocations = SnapshotMap::new();
        for base in live_allocations.keys() {
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
        // heap collections above, and forgets every cell nothing preserves,
        // exactly as the loop havoc does.
        let union_widths = union_overlay_widths(&self);
        std::sync::Arc::make_mut(&mut self.cells).retain(|pointer, value| {
            loan_preserving_havoc_keeps_cell(
                pointer,
                value,
                &union_widths,
                preserved_blocks,
                ledger,
            )
        });
        blocks.insert(format!("havoc:{}", variable.0).into(), CBlock::new(0));
        self.blocks = std::sync::Arc::new(blocks);
        std::sync::Arc::make_mut(&mut self.forgotten).ended_local_blocks = ended_local_blocks;
        self.heap = std::sync::Arc::new(CHeapMemory {
            live_allocations,
            deallocated_allocations,
            pending_allocations,
            uninitialized_allocations,
            initialized_cells,
            zeroed_allocations,
            zeroed_prefix_allocations,
            zeroed_pending_allocations,
            pending_reallocations,
        });
        Ok(self)
    }

    pub(in crate::kernel) fn with_call_memory_havoc(
        mut self,
        variable: Variable,
        mutable_ranges: &[CMemoryRange],
        assumptions: &PureFactContext,
    ) -> Self {
        let base = Some(intern_c_memory_ref(&self));
        call_havoc_candidates(mutable_ranges)
            .retain_map(std::sync::Arc::make_mut(&mut self.cells), |pointer, _| {
                call_havoc_keeps_cell(pointer, mutable_ranges, assumptions)
            });
        self.forget_zeroed_allocations_written_by(mutable_ranges, assumptions);
        std::sync::Arc::make_mut(&mut self.blocks).insert(
            format!("call-havoc:{}", variable.0).into(),
            CBlock::new(memory_havoc_write_set_fingerprint(mutable_ranges)),
        );
        // Keep the legacy marker's semantic shape and add a collision-free
        // structural key for the checked write set. This key is intentionally
        // not named as a havoc marker: canonical load snapshots must continue
        // to treat the call-havoc edge as the only global memory barrier.
        let identity = memory_havoc_write_set_identity(mutable_ranges);
        std::sync::Arc::make_mut(&mut self.blocks).insert(
            format!("call-write-set:{}:{identity}", variable.0).into(),
            CBlock::new(0),
        );
        if let Some(base) = base {
            record_c_memory_derivation(
                &self,
                CMemoryDerivation::CallHavoc {
                    base,
                    variable,
                    mutable_ranges: mutable_ranges.to_vec(),
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
    ) -> bool {
        if self.heap != before.heap || self.blocks.len() != before.blocks.len() + 2 {
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
        let write_set_marker: PointerBlock = format!(
            "call-write-set:{variable}:{}",
            memory_havoc_write_set_identity(mutable_ranges)
        )
        .into();
        if added_blocks.len() != 2
            || **marker_block != CBlock::new(memory_havoc_write_set_fingerprint(mutable_ranges))
            || self.blocks.get(&write_set_marker) != Some(&CBlock::new(0))
        {
            return false;
        }

        // The producer's rule, over the same candidates: every cell outside
        // them is kept by `call_havoc_keeps_cell`, so the expected result is
        // `before` without the candidates the rule drops, and the comparison
        // walks only the paths the two snapshots do not share.
        let candidates = call_havoc_candidates(mutable_ranges);
        let mut visited = 0usize;
        let dropped_cells = candidates
            .entries(&before.cells)
            .inspect(|_| visited += 1)
            .filter(|(pointer, _)| !call_havoc_keeps_cell(pointer, mutable_ranges, assumptions))
            .map(|(pointer, _)| pointer)
            .collect::<Vec<_>>();
        let dropped_union_cells = candidates
            .entries(&before.union_cells)
            .inspect(|_| visited += 1)
            .filter(|((pointer, _), _)| {
                !call_havoc_keeps_cell(pointer, mutable_ranges, assumptions)
            })
            .map(|(key, _)| key)
            .collect::<Vec<_>>();
        crate::instrumentation::record_deterministic_work(visited);
        self.cells.is_without(&before.cells, &dropped_cells)
            && self
                .union_cells
                .is_without(&before.union_cells, &dropped_union_cells)
    }

    pub fn store(self, pointer: Pointer, value: CValue) -> Self {
        self.store_with_context(pointer, value, &PureFactContext::new())
    }

    /// Cache the canonical value of an already existing cell for a resource
    /// projection. This is not a C write and cannot establish initialization.
    /// The conservative store edge keeps memory-DAG lookup connected without
    /// granting any new initialized-cell or allocation authority.
    pub(crate) fn materialize_named_cell(mut self, pointer: Pointer, value: CValue) -> Self {
        if self.cells.contains_key(&pointer) {
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
                && !self.has_initialized_cell_at(&pointer, value.byte_width())
            {
                return self;
            }
        }
        let base = intern_c_memory_ref(&self);
        std::sync::Arc::make_mut(&mut self.cells).insert(pointer.clone(), value.clone());
        record_c_memory_derivation(
            &self,
            CMemoryDerivation::Store {
                base,
                pointer,
                value,
            },
        );
        self
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
        let base = intern_c_memory_ref(&self);
        std::sync::Arc::make_mut(&mut self.cells).insert(pointer.clone(), value.clone());
        if self.is_live_heap_address(&pointer, context) {
            std::sync::Arc::make_mut(&mut self.heap)
                .initialized_cells
                .insert(pointer.clone(), value.byte_width());
        }
        // Skipped when empty so an ordinary store neither visits nor
        // reallocates the shared overlay map.
        if !self.union_cells.is_empty() {
            self.remove_union_views_at(&pointer);
        }
        record_c_memory_derivation(
            &self,
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
            Some(value) => CExpressionOutcome::Value(value.clone()),
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
            .diff(&other.cells)
            .map(|change| change.key().clone())
            .collect::<BTreeSet<_>>();
        pointers.extend(
            self.union_cells
                .diff(&other.union_cells)
                .map(|change| change.key().0.clone()),
        );
        pointers.into_iter().collect()
    }

    pub(in crate::kernel) fn known_value(&self, pointer: &Pointer) -> Option<CValue> {
        self.cells.get(pointer).cloned()
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

    /// Whether a typed scalar at this exact heap address was initialized
    /// before cached values were forgotten by a call or loop havoc.
    pub(in crate::kernel) fn has_initialized_cell_at(
        &self,
        pointer: &Pointer,
        byte_width: u32,
    ) -> bool {
        self.heap
            .initialized_cells
            .get(pointer)
            .is_some_and(|width| *width >= byte_width)
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
        let mut memory = self.without_possible_aliasing_cells(
            &written_pointer,
            written_bytes,
            &PureFactContext::new(),
        );
        let mut initialized_widths = BTreeMap::<Pointer, u32>::new();
        for (pointer, value_type, value) in views {
            std::sync::Arc::make_mut(&mut memory.union_cells)
                .insert((pointer.clone(), value_type), value);
            if memory.is_live_heap_address(&pointer, &PureFactContext::new()) {
                initialized_widths
                    .entry(pointer)
                    .and_modify(|width| *width = (*width).max(value_type.byte_width()))
                    .or_insert(value_type.byte_width());
            }
        }
        for (pointer, width) in initialized_widths {
            let initialized_cells =
                &mut std::sync::Arc::make_mut(&mut memory.heap).initialized_cells;
            let width = initialized_cells
                .get(&pointer)
                .map_or(width, |existing| (*existing).max(width));
            initialized_cells.insert(pointer, width);
        }
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
        own.retain_map(std::sync::Arc::make_mut(&mut memory.cells), |pointer, _| {
            !overlaps(pointer)
        });
        own.retain_map(
            std::sync::Arc::make_mut(&mut memory.union_cells),
            |(pointer, _), _| !overlaps(pointer),
        );
        own.retain_map(
            &mut std::sync::Arc::make_mut(&mut memory.heap).initialized_cells,
            |pointer, _| !overlaps(pointer),
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
        memory
    }

    pub(in crate::kernel) fn without_cell(&self, pointer: &Pointer) -> Self {
        let mut memory = self.clone();
        std::sync::Arc::make_mut(&mut memory.cells).remove(pointer);
        memory.remove_union_views_at(pointer);
        std::sync::Arc::make_mut(&mut memory.heap)
            .initialized_cells
            .remove(pointer);
        memory
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
        let base = Some(intern_c_memory_ref(self));
        let mut memory = self.clone();
        // Whether any cell went for the *aliasing* reason rather than because
        // this store overwrites every one of its bytes. An overwritten cell
        // is stale, not forgotten: the store about to run replaces exactly
        // what was dropped, so the result still says everything about the
        // state it describes. A possibly aliasing cell is knowledge the
        // result no longer has, and that is what has to show in the content.
        let mut forgot_live_knowledge = false;
        // Every cell in a block proven distinct from the written one is kept
        // by each ladder below (its bytes are `Separate` and its address is
        // proven distinct on the first rung), so only the candidates are
        // asked.
        let candidates = AliasCandidates::of_block(&normalized_pointer.block);
        candidates.retain_map(std::sync::Arc::make_mut(&mut memory.cells), |cell_pointer, cell_value| {
            let normalized_cell_pointer = Pointer {
                block: cell_pointer.block.clone(),
                offset: normalize_exact_memory_loads_in_pointer_offset(
                    &cell_pointer.offset,
                    assumptions,
                ),
            };
            if normalized_cell_pointer.block == normalized_pointer.block
                && written.as_ref().is_some_and(|written| {
                    written.overwrites(&normalized_cell_pointer, cell_value)
                })
            {
                // Only a cell the store writes *completely* is stale. One it
                // writes part of leaves the untouched bytes unrecorded, so the
                // result knows strictly less than its source and has to say so.
                forgot_live_knowledge |= !written.as_ref().is_some_and(|written| {
                    written.overwrites_completely(&normalized_cell_pointer, cell_value)
                });
                return false;
            }
            let address_inequality_separates_bytes = crate::kernel::reasoning::access_byte_overlap(
                &normalized_cell_pointer,
                crate::kernel::reasoning::cell_access_byte_width(cell_value),
                &normalized_pointer,
                bytes,
                assumptions,
            ) == crate::kernel::reasoning::AccessByteOverlap::Separate;
            let kept = address_inequality_separates_bytes
                && pointers_proven_distinct_for_memory_resolution(
                    &normalized_cell_pointer,
                    &normalized_pointer,
                    assumptions,
                )
                // The three range rungs. A field cell survives a store into
                // an array it is separated from: separation facts plus range
                // membership decide the cross-base pairs offset reasoning
                // cannot, and `access_byte_overlap` has no counterpart for
                // them — it answers `Unknown` for every pair with no common
                // additive base, which is exactly the pairs these exist to
                // decide. They place an access by its *first element*, so
                // they carry the same confusion one level up; that is
                // reported rather than fixed here, because the membership
                // evidence takes no access width and the retained
                // certificate has no field for one.
                || assumptions.pointers_proven_disjoint_by_explicit_range_for_memory_resolution(
                    &normalized_cell_pointer,
                    &normalized_pointer,
                )
                || assumptions
                    .pointers_directly_disjoint_by_range(&normalized_cell_pointer, &normalized_pointer)
                // Last: a separating composition owns the written address and
                // this cell's address through two different members, so the
                // partition invariant keeps the cell. Kept here beside the
                // range scan above, for the same reason: once the store has
                // dropped a cell, the two snapshots differ *at the read's own
                // address*, and no later framing route can recover it — the
                // question is only decidable while the cell is still there.
                || crate::kernel::memory_provenance::owned_composition_store_separated_evidence(
                    &normalized_pointer,
                    &normalized_cell_pointer,
                    assumptions,
                )
                .is_some();
            forgot_live_knowledge |= !kept;
            kept
        });
        candidates.retain_map(
            std::sync::Arc::make_mut(&mut memory.union_cells),
            |(cell_pointer, cell_type), _| {
                let normalized_cell_pointer = Pointer {
                    block: cell_pointer.block.clone(),
                    offset: normalize_exact_memory_loads_in_pointer_offset(
                        &cell_pointer.offset,
                        assumptions,
                    ),
                };
                if normalized_cell_pointer.block == normalized_pointer.block
                    && written.as_ref().is_some_and(|written| {
                        written.overwrites_typed(&normalized_cell_pointer, *cell_type)
                    })
                {
                    forgot_live_knowledge |= !written.as_ref().is_some_and(|written| {
                        written.overwrites_typed_completely(&normalized_cell_pointer, *cell_type)
                    });
                    return false;
                }
                // A union view has no value to read a width from, so it stands in
                // the width of the type it is keyed by — the access it records.
                let address_inequality_separates_bytes =
                    crate::kernel::reasoning::access_byte_overlap(
                        &normalized_cell_pointer,
                        cell_type.byte_width().max(1),
                        &normalized_pointer,
                        bytes,
                        assumptions,
                    ) == crate::kernel::reasoning::AccessByteOverlap::Separate;
                let kept = address_inequality_separates_bytes
                && pointers_proven_distinct_for_memory_resolution(
                    &normalized_cell_pointer,
                    &normalized_pointer,
                    assumptions,
                )
                || assumptions.pointers_directly_disjoint_by_range(
                    &normalized_cell_pointer,
                    &normalized_pointer,
                )
                || crate::kernel::memory_provenance::owned_composition_store_separated_evidence(
                    &normalized_pointer,
                    &normalized_cell_pointer,
                    assumptions,
                )
                .is_some();
                forgot_live_knowledge |= !kept;
                kept
            },
        );
        candidates.retain_map(
            &mut std::sync::Arc::make_mut(&mut memory.heap).initialized_cells,
            |cell_pointer, width| {
                let normalized_cell_pointer = Pointer {
                    block: cell_pointer.block.clone(),
                    offset: normalize_exact_memory_loads_in_pointer_offset(
                        &cell_pointer.offset,
                        assumptions,
                    ),
                };
                let separate = crate::kernel::reasoning::access_byte_overlap(
                    &normalized_cell_pointer,
                    *width,
                    &normalized_pointer,
                    bytes,
                    assumptions,
                ) == crate::kernel::reasoning::AccessByteOverlap::Separate;
                separate
                    && (pointers_proven_distinct_for_memory_resolution(
                        &normalized_cell_pointer,
                        &normalized_pointer,
                        assumptions,
                    ) || normalized_cell_pointer.block != normalized_pointer.block)
            },
        );
        // Forgetting nothing is not a transition: the memory is the same
        // snapshot, so a later load keeps resolving through it unchanged
        // instead of stopping at an edge that records no write.
        if memory.cells.len() == self.cells.len()
            && memory.union_cells.len() == self.union_cells.len()
            && memory.heap.initialized_cells == self.heap.initialized_cells
        {
            return self.clone();
        }
        if let Some(base) = base {
            // The mark goes on before interning, because it is what the
            // result is interned *as*. Without it the emptied cell map can
            // re-intern as an older node — in the smallest case the function
            // entry state — and then this edge would run backwards, be
            // dropped, and leave the store that filled those cells off every
            // recorded history.
            if forgot_live_knowledge {
                memory.mark_forgotten_from(&base);
                // The mark is what makes this edge recordable, so check it
                // where it is set rather than where it is used: a result
                // that is not younger than its base would be dropped by
                // `record_c_memory_derivation` and take the forgotten
                // store off every recorded history with it.
                debug_assert!(
                    intern_c_memory_ref(&memory).arena_id() > base.arena_id(),
                    "a forget that lost knowledge landed on an older snapshot"
                );
            }
            record_c_memory_derivation(&memory, CMemoryDerivation::CellsForgotten { base });
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
        self.cells
            .get(pointer)
            .is_some_and(|value| value.byte_width() == byte_width)
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
        ))
    }

    pub(in crate::kernel) fn symbolic_int8_load(&self, pointer: &Pointer) -> CValue {
        int8(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
        ))
    }

    pub(in crate::kernel) fn symbolic_int16_load(&self, pointer: &Pointer) -> CValue {
        int16(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
        ))
    }

    pub(in crate::kernel) fn symbolic_uint8_load(&self, pointer: &Pointer) -> CValue {
        uint8(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
        ))
    }

    pub(in crate::kernel) fn symbolic_uint16_load(&self, pointer: &Pointer) -> CValue {
        uint16(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
        ))
    }

    pub(in crate::kernel) fn symbolic_uint32_load(&self, pointer: &Pointer) -> CValue {
        uint32(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
        ))
    }

    pub(in crate::kernel) fn symbolic_int64_load(&self, pointer: &Pointer) -> CValue {
        CValue::Int64(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
        ))
    }

    pub(in crate::kernel) fn symbolic_uint64_load(&self, pointer: &Pointer) -> CValue {
        CValue::UInt64(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
        ))
    }

    pub(in crate::kernel) fn symbolic_float32_load(&self, pointer: &Pointer) -> CValue {
        CValue::Float32(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
        ))
    }

    pub(in crate::kernel) fn symbolic_float64_load(&self, pointer: &Pointer) -> CValue {
        CValue::Float64(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
        ))
    }

    pub(in crate::kernel) fn symbolic_pointer_load(
        &self,
        pointer: &Pointer,
        pointee_byte_width: u32,
        value_type: CType,
    ) -> CValue {
        CValue::typed_pointer(
            Pointer {
                block: pointer.block.clone(),
                offset: PointerOffsetTerm::scale_int32(
                    Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(self.clone()),
                        Box::new(pointer.clone()),
                    ),
                    i64::from(pointee_byte_width),
                ),
            },
            value_type,
        )
    }
}

impl CState {
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
    pub fn new() -> Self {
        Self::default()
    }

    pub(in crate::kernel) fn next_local_frame(&self) -> u64 {
        self.next_local_frame
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
            && std::sync::Arc::ptr_eq(&self.counted_populations, &other.counted_populations)
    }

    pub fn with_local(mut self, name: impl Into<String>, value: CValue) -> Self {
        self.locals.set(name, value);
        self
    }

    pub fn with_int32_array_local(mut self, name: impl Into<String>, length: u32) -> Self {
        self.locals.set_int32_array(name, length);
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
    pub(crate) fn set_memory(&mut self, memory: CMemory) {
        self.resources = self
            .resources
            .clone()
            .invalidate_memory_support(&self.memory, &memory);
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

    #[allow(dead_code)]
    pub(crate) fn loan_ledger(&self) -> Option<&crate::kernel::loans::LoanLedger> {
        self.loan_ledger.as_ref()
    }

    #[allow(dead_code)]
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

    /// The values held by memory-resident scalar locals at offset zero.
    /// Resolve names through the local-slot index so framed parameter blocks
    /// are exposed with their source name rather than their internal block id.
    pub fn local_cell_values(&self) -> impl Iterator<Item = (&str, &CValue)> {
        self.memory.cells.iter().filter_map(|(pointer, value)| {
            if pointer.offset != PointerOffsetTerm::Constant(0) {
                return None;
            }
            self.locals.name_for_slot(pointer).map(|name| (name, value))
        })
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
                memory.known_value(&slot).map(|value| {
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

    pub fn with_counted_population(
        mut self,
        name: impl Into<String>,
        arguments: ResourceArguments,
        count: Bitvector32Term,
    ) -> Self {
        let name = name.into();
        if let Some(population) = std::sync::Arc::make_mut(&mut self.counted_populations)
            .iter_mut()
            .find(|population| {
                !population.family_observation_marker
                    && population.name == name
                    && population.arguments == arguments
            })
        {
            population.count = count;
        } else {
            std::sync::Arc::make_mut(&mut self.counted_populations).push(CCountedPopulation {
                name,
                arguments,
                count,
                family_observation_marker: false,
            });
        }
        self
    }

    pub fn counted_population(
        &self,
        name: &str,
        arguments: &[AlgebraicValue],
    ) -> Option<&Bitvector32Term> {
        self.counted_populations
            .iter()
            .find(|population| {
                !population.family_observation_marker
                    && population.name == name
                    && population.arguments.as_ref() == arguments
            })
            .map(|population| &population.count)
    }

    pub fn counted_population_proven_equal(
        &self,
        name: &str,
        arguments: &[AlgebraicValue],
        assumptions: &PureFactContext,
    ) -> Option<(String, ResourceArguments, Bitvector32Term)> {
        self.counted_populations
            .iter()
            .find(|population| {
                !population.family_observation_marker
                    && population.name == name
                    && population.arguments.len() == arguments.len()
                    && population
                        .arguments
                        .iter()
                        .zip(arguments)
                        .all(|(left, right)| {
                            crate::kernel::resource_arguments_proven_equal(left, right, assumptions)
                        })
            })
            .map(|population| {
                (
                    population.name.clone(),
                    population.arguments.clone(),
                    population.count.clone(),
                )
            })
    }

    /// The total of every ledger entry this pattern names, or `None` where
    /// that total is not a count.
    ///
    /// The entries are populations and their counts are natural numbers, so
    /// the fold goes through `population_quantity_sum` rather than the
    /// modular add: two entries of `2000000000` are four billion units, and
    /// the wrapped `-294967296` would be a smaller number than either of
    /// them. `crate::kernel::spec`'s own pattern sum asks the same question
    /// with an obligation list to put the no-overflow condition on; this one
    /// has none, so it answers that the sum is not established.
    pub fn counted_population_sum(
        &self,
        name: &str,
        arguments: &[Option<AlgebraicValue>],
        assumptions: &PureFactContext,
    ) -> Option<Bitvector32Term> {
        self.counted_populations
            .iter()
            .filter(|population| {
                !population.family_observation_marker
                    && population.name == name
                    && population.arguments.len() == arguments.len()
                    && population
                        .arguments
                        .iter()
                        .zip(arguments)
                        .all(|(actual, expected)| {
                            expected.as_ref().is_none_or(|expected| {
                                crate::kernel::resource_arguments_proven_equal(
                                    actual,
                                    expected,
                                    assumptions,
                                )
                            })
                        })
            })
            .try_fold(Bitvector32Term::Constant(0), |total, population| {
                crate::kernel::primitives::resource_algebra::population_quantity_sum(
                    &total,
                    &population.count,
                    assumptions,
                )
            })
    }

    pub fn without_counted_population(mut self, name: &str, arguments: &[AlgebraicValue]) -> Self {
        std::sync::Arc::make_mut(&mut self.counted_populations).retain(|population| {
            population.family_observation_marker
                || population.name != name
                || population.arguments.as_ref() != arguments
        });
        self
    }

    pub fn counted_populations(&self) -> impl Iterator<Item = &CCountedPopulation> {
        self.counted_populations
            .iter()
            .filter(|population| !population.family_observation_marker)
    }

    pub fn with_observed_population_family(mut self, name: impl Into<String>) -> Self {
        let name = name.into();
        if !self.observes_population_family(&name) {
            std::sync::Arc::make_mut(&mut self.counted_populations).push(CCountedPopulation {
                name,
                arguments: std::sync::Arc::from([]),
                count: Bitvector32Term::Constant(0),
                family_observation_marker: true,
            });
        }
        self
    }

    pub fn observes_population_family(&self, name: &str) -> bool {
        self.counted_populations
            .iter()
            .any(|population| population.family_observation_marker && population.name == name)
    }

    /// The logical resource-state component used to index predicate facts.
    ///
    /// Predicate memory arguments retain their existing, explicit snapshot
    /// representation. Keeping memory and locals out of this value prevents
    /// an unrelated C step from changing the identity of a predicate merely
    /// because the predicate language can also observe resource counts.
    pub fn resource_state_snapshot(&self) -> Self {
        let observed_families = self
            .counted_populations
            .iter()
            .filter(|population| population.family_observation_marker)
            .map(|population| population.name.as_str())
            .collect::<BTreeSet<_>>();
        let counted_populations = self
            .counted_populations
            .iter()
            .filter(|population| {
                population.family_observation_marker
                    || observed_families.contains(population.name.as_str())
            })
            .cloned()
            .collect();
        Self {
            counted_populations: std::sync::Arc::new(counted_populations),
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

pub(crate) fn clear_block_alignment_registry() {
    BLOCK_ALIGNMENT_REGISTRY.with(|registry| registry.borrow_mut().clear());
}

thread_local! {
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
    static NEVER_ADDRESS_TAKEN_LOCALS: std::cell::RefCell<BTreeSet<String>> =
        const { std::cell::RefCell::new(BTreeSet::new()) };
}

/// Records the program-wide never-address-taken names for this session. The
/// surface computes them from every function body it parsed; see
/// `never_address_taken_local_names`.
pub(crate) fn set_never_address_taken_locals(names: BTreeSet<String>) {
    NEVER_ADDRESS_TAKEN_LOCALS.with(|registry| *registry.borrow_mut() = names);
}

/// Withdraws names a later source bundle shows to be address-taken, for a
/// verification that joins an enclosing session instead of starting one.
///
/// Returns whether anything was withdrawn, so the caller can drop the memo
/// tables that may already hold an answer computed while the name was still
/// in the registry. Today no caller joins a session with different sources,
/// and this keeps that from becoming a silent staleness bug if one appears.
pub(crate) fn withdraw_never_address_taken_locals(taken: &BTreeSet<String>) -> bool {
    NEVER_ADDRESS_TAKEN_LOCALS.with(|registry| {
        let mut registry = registry.borrow_mut();
        let before = registry.len();
        registry.retain(|name| !taken.contains(name));
        registry.len() != before
    })
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
    NEVER_ADDRESS_TAKEN_LOCALS.with(|registry| registry.borrow_mut().clear());
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
        assert!(memory.has_initialized_cell_at(&aliases[0], 4));
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
        assert!(!retired.has_initialized_cell_at(&aliases[0], 4));
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
mod hunt_investigation_join_dspelling_tests {
    use super::*;

    /// Investigation repro (bug hunt phase 2b): `with_interface_memory_havoc_preserving_loans`
    /// unions `live_allocations` keyed by pointer spelling, so one
    /// allocation recorded live by arm A under spelling P and by arm B
    /// through its proven-equal spelling Q joins as TWO live entries with
    /// no record of their equality. A free through each spelling then both
    /// succeed without any structure about their equal bases.
    #[test]
    fn hunt_investigation_join_carries_two_live_spellings_of_one_allocation() {
        let p = Pointer {
            block: PointerBlock::Heap(924_001),
            offset: PointerOffsetTerm::Constant(0),
        };
        let q = Pointer {
            block: PointerBlock::Heap(924_005),
            offset: PointerOffsetTerm::Constant(0),
        };
        let assumptions = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(p.clone(), q.clone()),
            true,
        ));
        // Arm A holds the allocation live under spelling p; arm B under q.
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
        assert!(joined.heap.live_allocations.contains_key(&p));
        assert!(joined.heap.live_allocations.contains_key(&q));
        // A free through each equal spelling is accepted as a plain C free.
        let once = joined
            .free_heap_block(&p, &assumptions)
            .expect("the first free is a real free");
        assert!(
            once.free_heap_block(&q, &assumptions).is_ok(),
            "BUG: freeing the same allocation through its second joined spelling succeeds"
        );
    }
}
