use super::*;
use crate::kernel::CheckedPopulationAuthorityExchange;
use crate::kernel::CheckedPopulationMemberExchange;
use crate::kernel::ResourceDescription;
#[cfg(test)]
use crate::kernel::binary_node;
use crate::kernel::population_authority::c_creation::is_external_population_anchor;
use crate::kernel::{CompareRelation, OverflowOperation};
use crate::kernel::{binary_term, unary_term};
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

/// Pushes a machine comparison or overflow test: its format, relation or
/// operation, and its operands.
fn push_havoc_comparison(
    identity: &mut String,
    tasks: &mut Vec<HavocIdentityTask>,
    op: BitvectorComparisonOp,
    left: Bitvector32Term,
    right: Bitvector32Term,
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
                other.c_symbol()
            );
            ""
        }
    };
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
                    Bitvector32Term::UInt32Constant(value) => {
                        let _ = write!(identity, "tuc{value};");
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
                    Bitvector32Term::Unary {
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
                    Bitvector32Term::Binary {
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
                    Bitvector32Term::BoolCast { to, value } => {
                        let _ = write!(identity, "tbcast{to:?}(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Condition(*value));
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
                    Bitvector32Term::PointerAddress(pointer, _) => {
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
                    ConditionTerm::PointerValueEqual(left, right) => {
                        let _ = write!(identity, "pveq({left:?},{right:?});");
                    }

                    ConditionTerm::AlgebraicEqual(left, right) => {
                        let _ = write!(identity, "aeq({left:?},{right:?});");
                    }
                    ConditionTerm::Constant(value) => {
                        let _ = write!(identity, "cc{value};");
                    }
                    ConditionTerm::Variable(variable) => {
                        let _ = write!(identity, "cv{};", variable.0);
                    }
                    ConditionTerm::Compare {
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
                    ConditionTerm::Overflows {
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
                    // As a word-valued Click application: by its hash.
                    ConditionTerm::BoolApplication(application) => {
                        use std::hash::{Hash, Hasher};
                        let mut hasher = std::collections::hash_map::DefaultHasher::new();
                        application.hash(&mut hasher);
                        let _ = write!(identity, "bclick:{:x};", hasher.finish());
                    }
                    ConditionTerm::BoolIf {
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
                    ConditionTerm::BoolEqual(left, right) => {
                        identity.push_str("beq(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Condition(*right));
                        tasks.push(HavocIdentityTask::Text(","));
                        tasks.push(HavocIdentityTask::Condition(*left));
                    }
                    ConditionTerm::BoolLoad(_, pointer) => {
                        identity.push_str("bload(");
                        tasks.push(HavocIdentityTask::Text(")"));
                        tasks.push(HavocIdentityTask::Pointer(*pointer));
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
            binary_node!(
                Int32,
                Add,
                Box::new(Bitvector32Term::Constant(0)),
                Box::new(term)
            )
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

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/primitives/memory_state/havoc_identity_tests.rs");
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
    /// `None` for an array whose elements have no pointer type of their own,
    /// as [`Self::array_object_values`] leaves it out.
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
                element_type.pointer_to()?,
                *constant,
            ),
            *element_type,
        ))
    }

    /// Each local array as a pointer to its first element, with the element
    /// type. An array whose elements have no pointer type of their own, such
    /// as `const char *const *t[]`, has no such pointer value and is left
    /// out: a proof cannot name it, though execution reads it.
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
                        element_type.pointer_to()?,
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

    /// The array objects whose slots lie in `block`, with their element
    /// types and slots, found through the slot index as
    /// [`Self::names_with_slot_in`] finds them.
    pub(crate) fn array_objects_with_slot_in(
        &self,
        block: &PointerBlock,
    ) -> Vec<(&str, CType, &Pointer)> {
        self.names_with_slot_in(block)
            .into_iter()
            .filter_map(|name| match self.binding(name)? {
                CLocalBinding::ArrayObject {
                    element_type, slot, ..
                } => Some((name, *element_type, slot)),
                _ => None,
            })
            .collect()
    }

    /// The names whose slots lie in `block`, found through the slot index:
    /// pointers order by block first, so they are one run of slot keys.
    pub(in crate::kernel) fn names_with_slot_in(&self, block: &PointerBlock) -> Vec<&str> {
        let mut names = Vec::new();
        let mut at = Pointer {
            block: block.clone(),
            offset: PointerOffsetTerm::Constant(i64::MIN),
        };
        if let Some(name) = self.slots.get(&at) {
            names.push(name.as_str());
        }
        while let Some((pointer, name)) = self.slots.get_greater_than(&at) {
            if &pointer.block != block {
                break;
            }
            names.push(name.as_str());
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
    ) -> impl Iterator<Item = &'a str> + 'a {
        self.bindings.diff(&other.bindings).map(|(name, _, _)| {
            crate::instrumentation::record_deterministic_work(1);
            name.as_str()
        })
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

fn held_pointer_block(binding: &CLocalBinding) -> Option<&PointerBlock> {
    match binding {
        CLocalBinding::Object {
            value: CValue::Pointer(pointer),
            ..
        } => Some(&pointer.block),
        _ => None,
    }
}

/// The numeric value of a scalar of integer or truth type.
fn held_integer_term(binding: &CLocalBinding) -> Option<&Bitvector32Term> {
    let CLocalBinding::Object { value, .. } = binding else {
        return None;
    };
    match value.numeric_value() {
        CValue::Bool(term)
        | CValue::Int8(term)
        | CValue::Int16(term)
        | CValue::Int32(term)
        | CValue::UInt8(term)
        | CValue::UInt16(term)
        | CValue::UInt32(term)
        | CValue::Int64(term)
        | CValue::UInt64(term)
        | CValue::Int128(term)
        | CValue::UInt128(term) => Some(term),
        _ => None,
    }
}

/// A constant-time fingerprint of a term: its root's variant and, for a
/// variable or constant, its payload, and for a format-carrying operator its
/// format and operator, and the same of a binary node's two
/// operands. Equal terms share a fingerprint; a lookup compares the terms
/// it finds, so a shared fingerprint costs only a comparison.
pub(crate) fn held_term_fingerprint(term: &Bitvector32Term) -> u64 {
    use std::hash::{Hash, Hasher};
    fn atom(term: &Bitvector32Term, hasher: &mut impl Hasher) {
        std::mem::discriminant(term).hash(hasher);
        match term {
            Bitvector32Term::Variable(variable) => variable.hash(hasher),
            Bitvector32Term::Constant(value) | Bitvector32Term::UInt32Constant(value) => {
                value.hash(hasher)
            }
            Bitvector32Term::Binary { format, op, .. } => (format, op).hash(hasher),
            Bitvector32Term::Unary { format, op, .. } => (format, op).hash(hasher),
            _ => {}
        }
    }
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    atom(term, &mut hasher);
    if let Some((_, left, right)) = term.as_binary() {
        atom(left, &mut hasher);
        atom(right, &mut hasher);
    }
    hasher.finish()
}

impl CLocalEnvironment {
    /// An environment of these bindings and slots, with its held-term index
    /// built from the bindings.
    pub(in crate::kernel) fn from_parts(
        bindings: crate::persistent::PersistentMap<String, CLocalBinding>,
        slots: crate::persistent::PersistentMap<Pointer, String>,
    ) -> Self {
        let held_terms = bindings
            .iter()
            .filter_map(|(name, binding)| {
                held_integer_term(binding)
                    .map(|term| ((held_term_fingerprint(term), name.clone()), ()))
            })
            .collect();
        let mut pointer_objects_by_block = crate::persistent::PersistentMap::<
            PointerBlock,
            crate::persistent::PersistentMap<String, ()>,
        >::default();
        for (name, binding) in bindings.iter() {
            if let Some(block) = held_pointer_block(binding) {
                let mut names = pointer_objects_by_block
                    .get(block)
                    .cloned()
                    .unwrap_or_default();
                names.insert(name.clone(), ());
                pointer_objects_by_block.insert(block.clone(), names);
            }
        }
        Self {
            bindings,
            slots,
            held_terms,
            pointer_objects_by_block,
        }
    }

    pub(in crate::kernel) fn insert_binding(&mut self, name: String, binding: CLocalBinding) {
        let slot = binding.slot().clone();
        let old = self.bindings.get(&name);
        let old_slot = old.map(CLocalBinding::slot).cloned();
        let old_held = old.and_then(held_integer_term).map(held_term_fingerprint);
        let new_held = held_integer_term(&binding).map(held_term_fingerprint);
        let old_block = old.and_then(held_pointer_block).cloned();
        let new_block = held_pointer_block(&binding);
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
        }
        self.slots.insert(slot, name);
    }

    fn remove_pointer_object(&mut self, block: &PointerBlock, name: &str) {
        let Some(mut names) = self.pointer_objects_by_block.get(block).cloned() else {
            return;
        };
        names.remove(&name.to_string());
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
        block: &PointerBlock,
    ) -> impl Iterator<Item = (&'a str, &'a CPointerValue)> {
        self.pointer_objects_by_block
            .get(block)
            .into_iter()
            .flat_map(|names| names.iter())
            .map(|(name, ())| {
                let Some(CValue::Pointer(pointer)) = self.get(name) else {
                    unreachable!("pointer object index follows its binding")
                };
                (name.as_str(), pointer)
            })
    }

    /// The names, in name order, of the scalar objects holding exactly
    /// `term`: the index narrows the candidates to those sharing its
    /// fingerprint, and each is compared with `term`.
    pub(crate) fn names_holding_integer<'a, 't>(
        &'a self,
        term: &'t Bitvector32Term,
    ) -> impl Iterator<Item = &'a str> + use<'a, 't> {
        let fingerprint = held_term_fingerprint(term);
        let mut at = Some((fingerprint, String::new()));
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
                if *found_fingerprint != fingerprint {
                    return None;
                }
                at = Some((fingerprint, name.clone()));
                crate::instrumentation::record_deterministic_work(1);
                if self.bindings.get(name).and_then(held_integer_term) == Some(term) {
                    return Some(name.as_str());
                }
            }
        })
    }

    /// The scalar objects whose held integer term differs from `earlier`'s,
    /// with the term each holds now: every scalar object when there is no
    /// earlier environment. Shared subtrees are skipped, so for environments
    /// derived from one another the walk visits only the changed bindings.
    pub(crate) fn changed_integer_holdings<'a>(
        &'a self,
        earlier: Option<&'a Self>,
    ) -> Vec<(&'a str, &'a Bitvector32Term)> {
        let changed =
            |name: &'a String, now: Option<&'a CLocalBinding>, before: Option<&CLocalBinding>| {
                let held = held_integer_term(now?)?;
                (before.and_then(held_integer_term) != Some(held)).then_some((name.as_str(), held))
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
    pub(crate) fn changed_pointer_blocks<'a>(
        &'a self,
        earlier: Option<&'a Self>,
    ) -> Vec<(&'a str, &'a PointerBlock)> {
        let changed = |name: &'a String,
                       now: Option<&'a CLocalBinding>,
                       before: Option<&CLocalBinding>| {
            let block = held_pointer_block(now?)?;
            (before.and_then(held_pointer_block) != Some(block)).then_some((name.as_str(), block))
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
    pub(crate) fn holds_pointer_in_block(&self, name: &str, block: &PointerBlock) -> bool {
        self.bindings.get(name).and_then(held_pointer_block) == Some(block)
    }

    /// Whether the scalar object `name` holds exactly `term`.
    pub(crate) fn holds_integer(&self, name: &str, term: &Bitvector32Term) -> bool {
        self.bindings.get(name).and_then(held_integer_term) == Some(term)
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
        let Some(binding) = self.bindings.get(name).cloned() else {
            return;
        };
        if let Some(term) = held_integer_term(&binding) {
            self.held_terms
                .remove(&(held_term_fingerprint(term), name.to_string()));
        }
        if let Some(block) = held_pointer_block(&binding) {
            self.remove_pointer_object(block, name);
        }
        self.bindings.remove(&name.to_string());
        self.slots.remove(binding.slot());
    }
}

impl CBlock {
    pub fn new(size: u32) -> Self {
        Self {
            size: Bitvector32Term::Constant(size),
            read_only: false,
            declared_scalar_type: None,
            declared_class: None,
        }
    }

    pub fn read_only(size: u32) -> Self {
        Self {
            size: Bitvector32Term::Constant(size),
            read_only: true,
            declared_scalar_type: None,
            declared_class: None,
        }
    }

    pub(in crate::kernel) fn with_symbolic_size(size: Bitvector32Term) -> Self {
        Self {
            size,
            read_only: false,
            declared_scalar_type: None,
            declared_class: None,
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
/// [`CMemoryDerivation::CallHavoc`].
#[derive(Clone, Debug)]
pub struct CallKeptRanges {
    ranges: ResourceContext,
    residual: Option<ResourceContext>,
    identity: std::sync::Arc<KeptRangeSet>,
    premises: Vec<(ConditionTerm, bool)>,
    /// The definitions, sorted by name, of the residual's composite families
    /// whose bodies are argument-direct. Their composites are not opened at
    /// the call: the ranges a question about one address needs are opened
    /// from the residual's composites whose arguments can spell it
    /// ([`Self::range_holding`]), and the identity names the composites.
    direct: Option<std::sync::Arc<Vec<CCompositeResourceDefinition>>>,
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
    ranges: SnapshotMap<CMemoryRange, ()>,
    /// The residual's owned composites, with multiplicity, when some of
    /// their ranges are answered per address rather than listed in `ranges`.
    composites: SnapshotMap<CResourceFact, usize>,
    original_memory: SnapshotMap<CResourceFact, ()>,
    introduced_composites: SnapshotMap<CResourceFact, usize>,
    // Share the flat input index, including views, without enumerating it.
    memory_inputs: SnapshotMap<CResourceFact, ()>,
}

impl PartialEq for CallKeptRanges {
    fn eq(&self, other: &Self) -> bool {
        self.identity.id == other.identity.id && self.premises == other.premises
    }
}
impl Eq for CallKeptRanges {}

fn intern_kept_range_set(
    ranges: SnapshotMap<CMemoryRange, ()>,
    composites: SnapshotMap<CResourceFact, usize>,
) -> std::sync::Arc<KeptRangeSet> {
    intern_kept_range_set_with_exclusions(
        ranges,
        composites,
        SnapshotMap::new(),
        SnapshotMap::new(),
        SnapshotMap::new(),
    )
}

fn intern_kept_range_set_with_exclusions(
    ranges: SnapshotMap<CMemoryRange, ()>,
    composites: SnapshotMap<CResourceFact, usize>,
    original_memory: SnapshotMap<CResourceFact, ()>,
    introduced_composites: SnapshotMap<CResourceFact, usize>,
    memory_inputs: SnapshotMap<CResourceFact, ()>,
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
    ranges: SnapshotMap<CMemoryRange, ()>,
    composites: SnapshotMap<CResourceFact, usize>,
    hash: u64,
) -> std::sync::Arc<KeptRangeSet> {
    intern_kept_range_set_with_exclusions_and_hash(
        ranges,
        composites,
        SnapshotMap::new(),
        SnapshotMap::new(),
        SnapshotMap::new(),
        hash,
    )
}

fn intern_kept_range_set_with_exclusions_and_hash(
    ranges: SnapshotMap<CMemoryRange, ()>,
    composites: SnapshotMap<CResourceFact, usize>,
    original_memory: SnapshotMap<CResourceFact, ()>,
    introduced_composites: SnapshotMap<CResourceFact, usize>,
    memory_inputs: SnapshotMap<CResourceFact, ()>,
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

impl CallKeptRanges {
    pub(in crate::kernel) fn new(
        ranges: ResourceContext,
        premises: Vec<(ConditionTerm, bool)>,
        direct: Option<std::sync::Arc<Vec<CCompositeResourceDefinition>>>,
    ) -> Self {
        let identity = intern_kept_range_set(
            ranges.flat_owned_memory_ranges().clone(),
            SnapshotMap::new(),
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
            SnapshotMap::new()
        };
        let introduced_composites = if let Some(original) = &self.caller_before_transfer {
            let before = original.owned_composite_facts();
            let after = residual.owned_composite_facts();
            let mut introduced = ResourceContext::new();
            for change in before.diff(after) {
                crate::instrumentation::record_deterministic_work(1);
                let fact = match change {
                    SnapshotMapChange::Added(fact) => fact,
                    SnapshotMapChange::Changed(fact) if after.get(fact) > before.get(fact) => fact,
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
    fn direct_ranges(&self, fact: &CResourceFact) -> Vec<CMemoryRange> {
        let (Some(direct), CResource::Composite { name, .. }) = (&self.direct, fact.resource())
        else {
            return Vec::new();
        };
        let Ok(index) = direct.binary_search_by(|definition| definition.name().cmp(name)) else {
            return Vec::new();
        };
        crate::kernel::functions::argument_direct_composite_ranges(
            fact,
            std::slice::from_ref(&direct[index]),
        )
    }

    /// Recorded caller ranges, for snapshot diagnostics: the listed
    /// ranges and those of every argument-direct composite.
    pub(crate) fn diagnostic_ranges(&self) -> ResourceContext {
        let mut ranges = self.identity.ranges.clone();
        for fact in self.identity.composites.keys() {
            for range in self.direct_ranges(fact) {
                ranges.insert(range, ());
            }
        }
        ResourceContext::new()
            .unchecked_with_facts(ranges.keys().cloned().map(CResourceFact::own_memory))
            .unchecked_with_facts(
                self.identity
                    .memory_inputs
                    .keys()
                    .filter(|fact| fact.is_view())
                    .cloned(),
            )
    }

    /// Recorded placement premises, for snapshot diagnostics.
    pub(crate) fn diagnostic_premises(&self) -> &[(ConditionTerm, bool)] {
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

    /// Whether `range` is kept: listed, or a range of an argument-direct
    /// composite whose arguments spell its base.
    pub(in crate::kernel) fn contains_range(&self, range: &CMemoryRange) -> bool {
        if self.identity.ranges.contains_key(range)
            || self
                .identity
                .memory_inputs
                .contains_key(&CResourceFact::view_memory(range.clone()))
        {
            return true;
        }
        let Some(residual) = self.direct.as_ref().and(self.residual.as_ref()) else {
            return false;
        };
        crate::kernel::assumptions::additive_base_spellings(range.base())
            .iter()
            .flat_map(|base| residual.owned_composites_with_pointer_argument(base))
            .any(|fact| self.direct_ranges(fact).contains(range))
    }

    /// The kept range holding the access. `placement` is the premises already
    /// assumed into `assumptions`, when the caller has built it once.
    ///
    /// The listed ranges are asked first. Then the argument-direct
    /// composites that can hold the access are opened: those with a pointer
    /// argument equal to an additive base spelling of `pointer` or an exact
    /// alias of one, and failing those, the ones with an argument in the
    /// access's block, as the listed ranges' own block fallback reads them
    /// ([`PureFactContext::kept_range_holding_access`]). Only those are
    /// opened, never the residual's other composites.
    pub(in crate::kernel) fn range_holding(
        &self,
        assumptions: &PureFactContext,
        placement: Option<&PureFactContext>,
        pointer: &Pointer,
        bytes: u32,
    ) -> Option<CMemoryRange> {
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
                let spellings = crate::kernel::assumptions::additive_base_spellings(pointer);
                let mut bases = spellings.clone();
                for spelling in &spellings {
                    bases.extend(assumptions.exact_pointer_aliases(spelling).cloned());
                }
                // Exclusive owners in the caller's original composition cannot
                // overlap. Once the flat caller frame has failed above, an
                // original flat owner rules out every unchanged composite.
                // A transferred owner may have been repackaged into a new
                // composite, so retain those candidates rather than declaring
                // the access changed merely from a mutable-range summary.
                let residual = if self
                    .caller_before_transfer
                    .as_ref()
                    .is_some_and(|original| {
                        bases.iter().any(|base| {
                            original
                                .owned_memory_members_with_base(base)
                                .any(|(_, range)| {
                                    original
                                        .exact_resource_facts(&CResource::Memory(range.clone()))
                                        .into_iter()
                                        .any(|fact| fact.has_proven_positive_quantity(assumptions))
                                        && assumptions
                                            .kept_range_holds_access(range, pointer, bytes)
                                })
                        })
                    }) {
                    &self.introduced_composites
                } else {
                    residual
                };
                let opened = |facts: &mut dyn Iterator<Item = &CResourceFact>| {
                    let mut seen = BTreeSet::new();
                    let mut ranges = Vec::new();
                    for fact in facts {
                        if seen.insert(fact.clone()) {
                            ranges.extend(self.direct_ranges(fact));
                        }
                    }
                    ResourceContext::new_with_equalities(assumptions)
                        .unchecked_with_facts(ranges.into_iter().map(CResourceFact::own_memory))
                };
                query(
                    &opened(
                        &mut bases
                            .iter()
                            .flat_map(|base| residual.owned_composites_with_pointer_argument(base)),
                    ),
                    false,
                )
                .or_else(|| {
                    let mut blocks = BTreeSet::from([&pointer.block]);
                    blocks.extend(bases.iter().map(|base| &base.block));
                    query(
                        &opened(&mut blocks.into_iter().flat_map(|block| {
                            residual.owned_composites_with_argument_block(block)
                        })),
                        false,
                    )
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
    /// bodies. The write-set marker spells both, so a content-equal snapshot
    /// whose edge was recorded first carries the same ones.
    pub(in crate::kernel) fn recorded_on(
        after: &CMemory,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        let kept = CallKeptRanges::recorded_on(after)?;
        // Use the exact residual snapshot recorded by the producer;
        // the opened-body ranges and premises remain in `kept`.
        let residual = kept.residual.clone().unwrap_or_default();
        Some(Self::new(residual, kept, assumptions))
    }

    /// The readable member that holds every byte of the access, from the opened
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
    pointer: &Pointer,
    value: &CValue,
    mutable_ranges: &[CMemoryRange],
    assumptions: &PureFactContext,
    kept: Option<&CallKeptOwnership>,
    preserve_local_slots: bool,
) -> CallHavocCellRule {
    if preserve_local_slots
        && pointer.block.is_local_block()
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

/// Membership in the blocks a memory join keeps: a set, or a query a join
/// answers from the state's own indexes without listing every block.
pub(crate) trait BlockMembership {
    fn contains_block(&self, block: &PointerBlock) -> bool;
}

impl BlockMembership for BTreeSet<PointerBlock> {
    fn contains_block(&self, block: &PointerBlock) -> bool {
        self.contains(block)
    }
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
    preserved_blocks: &dyn BlockMembership,
    ledger: Option<&crate::kernel::loans::LoanLedger>,
) -> bool {
    preserved_blocks.contains_block(&pointer.block)
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
    preserved_blocks: &dyn BlockMembership,
    ledger: Option<&crate::kernel::loans::LoanLedger>,
) -> (SlotSet, crate::kernel::primitives::RuleAnswer) {
    let exact = crate::kernel::primitives::RuleAnswer::Exact;
    if preserved_blocks.contains_block(&run.base().block) {
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
/// answered `false` here. That negative answer is not separation evidence:
/// the free-retirement path separately requires separation before keeping a
/// cached cell, and clears whole blocks for known aliases of the base.
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

    external_argument_offset_derives_from(base, pointer)
}

/// Whether `pointer`, in the external argument block, is `base` or an address
/// built by adding to `base`'s offset.
fn external_argument_offset_derives_from(base: &Pointer, pointer: &Pointer) -> bool {
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
        if block.is_havoc_block() || block.is_call_havoc_block() {
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
            .is_some_and(|block| block.declared_scalar_type.is_some())
    }

    /// The declared class of the object `pointer` lies in, when its block
    /// records one (`design/effective-types.md`).
    pub(in crate::kernel) fn declared_class(
        &self,
        pointer: &Pointer,
    ) -> Option<crate::kernel::effective_type::CAccessClass> {
        crate::instrumentation::record_deterministic_work(1);
        self.blocks.get(&pointer.block)?.declared_class.clone()
    }

    /// The effective type a C store gave the heap cell starting at
    /// `pointer`, while the cell still holds the value that store wrote
    /// (`design/effective-types.md`).
    pub(in crate::kernel) fn heap_effective_class(
        &self,
        pointer: &Pointer,
    ) -> Option<crate::kernel::effective_type::CAccessClass> {
        if !matches!(pointer.block, PointerBlock::Heap(_)) {
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
        pointer: &Pointer,
        width: u32,
        class: Option<crate::kernel::effective_type::CAccessClass>,
        value: &CValue,
    ) -> Self {
        if !matches!(pointer.block, PointerBlock::Heap(_)) {
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
        block: PointerBlock,
        declared_class: Option<crate::kernel::effective_type::CAccessClass>,
        size: u32,
    ) -> Self {
        self.with_classed_block_or_read_only(block, declared_class, size, false)
    }

    pub(in crate::kernel) fn with_classed_block_or_read_only(
        self,
        block: PointerBlock,
        declared_class: Option<crate::kernel::effective_type::CAccessClass>,
        size: u32,
        read_only: bool,
    ) -> Self {
        let Some(declared_class) = declared_class else {
            return self.with_block_or_read_only(block, size, read_only);
        };
        let mut memory = self;
        let base = intern_derivation_base(&mut memory);
        let mut declaration = CBlock::new(size);
        declaration.declared_class = Some(declared_class);
        declaration.read_only = read_only;
        std::sync::Arc::make_mut(&mut memory.blocks).insert(block.clone(), declaration);
        record_c_memory_derivation(
            &mut memory,
            CMemoryDerivation::BlockDeclared { base, block },
        );
        memory
    }

    /// [`Self::with_classed_scalar_block`] with the class its kernel type
    /// gives.
    #[cfg(test)]
    pub(in crate::kernel) fn with_declared_scalar_block(
        self,
        block: PointerBlock,
        size: u32,
        c_type: CType,
    ) -> Self {
        self.with_classed_scalar_block(block, size, c_type, None)
    }

    /// Declares one complete automatic scalar, retaining its type while its
    /// cells are unwritten, forgotten, or accessed through character pointers.
    /// The scalar's declared class is `declared_class`, or what its kernel
    /// type gives (`design/effective-types.md`).
    pub(in crate::kernel) fn with_classed_scalar_block(
        mut self,
        block: PointerBlock,
        size: u32,
        c_type: CType,
        declared_class: Option<crate::kernel::effective_type::CAccessClass>,
    ) -> Self {
        let base = intern_derivation_base(&mut self);
        let mut declaration = CBlock::new(size);
        declaration.declared_scalar_type = Some(c_type);
        declaration.declared_class = declared_class
            .or_else(|| crate::kernel::effective_type::CAccessClass::of_kernel_type(c_type));
        std::sync::Arc::make_mut(&mut self.blocks).insert(block.clone(), declaration);
        record_c_memory_derivation(&mut self, CMemoryDerivation::BlockDeclared { base, block });
        self
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
        assert!(declaration.declared_scalar_type.is_some());
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

    /// The extent of an unwritten footprint whose length is not a constant,
    /// such as `owns uninitialized(p[0..n])`: every byte from its start to the
    /// end of the block is treated as possibly unwritten. That is
    /// conservative for other memory of the same block, which then needs
    /// write or `defined` evidence too.
    pub(crate) const UNBOUNDED_UNWRITTEN_EXTENT: u32 = u32::MAX;

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

    /// A conservative overlap query over only potentially aliasing tracked
    /// objects. Different symbolic spellings do not establish separation.
    pub(in crate::kernel) fn may_read_uninitialized_object(
        &self,
        pointer: &Pointer,
        bytes: u32,
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
                // Array parameters share the external argument block. As for
                // a heap allocation there, a read belongs to the object only
                // when its address is built from the object's own base; any
                // other parameter's memory is held by a resource of its own,
                // which a valid context keeps disjoint from this one.
                if base.block == PointerBlock::ExternalArgument
                    && pointer.block == PointerBlock::ExternalArgument
                {
                    return external_argument_offset_derives_from(base, pointer);
                }
                true
            },
        )
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
    /// Gives a synthetic block the declared class of the storage it stands
    /// for (`design/effective-types.md`). Synthetic memories record no
    /// derivation, so the class needs none either.
    pub(in crate::kernel) fn with_block_declared_class(
        mut self,
        block: &PointerBlock,
        class: crate::kernel::effective_type::CAccessClass,
    ) -> Self {
        if let Some(mut declaration) = self.blocks.get(block).cloned() {
            let diagnostic_base = self.clone();
            declaration.declared_class = Some(class);
            std::sync::Arc::make_mut(&mut self.blocks).insert(block.clone(), declaration);
            self.record_diagnostic_transform(
                "declare block access class",
                vec![diagnostic_base],
                vec![CValue::pointer(Pointer {
                    block: block.clone(),
                    offset: PointerOffsetTerm::Constant(0),
                })],
            );
        }
        self
    }

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

    pub(in crate::kernel) fn free_heap_block(
        self,
        pointer: &Pointer,
        assumptions: &PureFactContext,
    ) -> Result<Self, CInvalidFree> {
        self.free_heap_block_with_owned_frame(pointer, assumptions, &ResourceContext::new())
    }

    /// Apply a free after execution consumed its full allocation ownership.
    /// `kept_owners` is the checked residual frame, never the input context:
    /// its owners coexist with the consumed bytes and survive their retirement.
    pub(in crate::kernel) fn free_heap_block_with_owned_frame(
        self,
        pointer: &Pointer,
        assumptions: &PureFactContext,
        kept_owners: &ResourceContext,
    ) -> Result<Self, CInvalidFree> {
        self.free_heap_block_and_owned_pointer_frames(pointer, assumptions, kept_owners)
            .map(|(memory, _)| memory)
    }

    /// The retained pointer cells whose frames need the checked ownership
    /// context, collected by the free's own retention decision. The executor
    /// names their two reads and publishes their equalities beside the free.
    pub(in crate::kernel) fn free_heap_block_and_owned_pointer_frames(
        mut self,
        pointer: &Pointer,
        assumptions: &PureFactContext,
        kept_owners: &ResourceContext,
    ) -> Result<(Self, Vec<(Pointer, CType)>), CInvalidFree> {
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
        // Absence from the retirement set is not separation: a different
        // block spelling may be an interior alias of this allocation.
        // The executor has consumed the allocation's complete ownership and
        // checked the surviving frame. Its remaining owners are separate
        // from those consumed bytes by construction. Select the owner of
        // this complete cell through the access index; do not rediscover the
        // freed extent's ownership (which may have symbolic size).
        let mut pointer_frames = Vec::new();
        self.forget_cached_values(
            ForgetScope::candidates(&candidates),
            |cell, value| {
                if aliased_blocks.contains(&cell.block) || freed_within(cell) {
                    CachedValueFate::Retired
                } else if pointer.blocks_proven_distinct(cell) {
                    CachedValueFate::Kept
                } else if kept_owners
                    .owned_memory_member_covering_access(cell, value.byte_width(), assumptions)
                    .is_some()
                {
                    let value_type = match value {
                        CachedValue::Cell(value) => value.c_type(),
                        CachedValue::UnionView(value_type, _) => value_type,
                    };
                    // Function pointers do not yet use logical version reads.
                    if value_type.pointee_type().is_some()
                        && !matches!(value_type, CType::FunctionPointer(_))
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
            record_c_memory_derivation(
                &mut self,
                CMemoryDerivation::HeapFreed {
                    base,
                    allocation_base: pointer.clone(),
                    bytes: bytes.clone(),
                },
            );
        }
        Ok((self, pointer_frames))
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

    pub(in crate::kernel) fn with_pending_heap_allocation(
        self,
        base: Pointer,
        bytes: Bitvector32Term,
        zeroed: bool,
    ) -> Self {
        self.with_pending_typed_heap_allocation(base, bytes, zeroed, None)
    }

    pub(in crate::kernel) fn with_pending_typed_heap_allocation(
        mut self,
        base: Pointer,
        bytes: Bitvector32Term,
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
        old_pointer: Pointer,
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
                CValue::pointer(old_pointer.clone()),
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

    /// Name the success identity already reserved by this allocation producer.
    /// This is a value observation, not evidence that allocation succeeded or
    /// that the object is still live. No facts or memory history are consulted.
    pub(crate) fn fresh_allocation_identity(
        &self,
        result: &CPointerValue,
    ) -> Option<CPointerValue> {
        let base = result.pointer();
        match base.block {
            PointerBlock::Heap(_) => Some(result.clone()),
            PointerBlock::Symbolic(variable)
                if self.heap.pending_allocations.contains_key(base) =>
            {
                let resolved = Pointer {
                    block: PointerBlock::Heap(variable.0),
                    offset: PointerOffsetTerm::Constant(0),
                };
                Some(crate::kernel::eval::rebase_resolved_allocation(
                    result, base, &resolved,
                ))
            }
            _ => None,
        }
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

    /// Whether heap identity `identity` had been handed out by this
    /// snapshot: live, freed, or pending. Identities are never reused within
    /// a proof, so an identity this answers false for is allocated after it.
    /// Allocation bases sit at offset zero, so each record is one lookup.
    pub(in crate::kernel) fn heap_identity_allocated(&self, identity: u64) -> bool {
        let base = |block| Pointer {
            block,
            offset: PointerOffsetTerm::Constant(0),
        };
        self.blocks.contains_key(&PointerBlock::Heap(identity))
            || self
                .heap
                .deallocated_allocations
                .contains_key(&base(PointerBlock::Heap(identity)))
            || self
                .heap
                .pending_allocations
                .contains_key(&base(PointerBlock::Symbolic(Variable(identity))))
    }

    /// Every heap identity [`Self::heap_identity_allocated`] answers true
    /// for, ascending. Costs the heap records this snapshot holds.
    pub(in crate::kernel) fn allocated_heap_identities(&self) -> Vec<u64> {
        let heap_base = |identity| Pointer {
            block: PointerBlock::Heap(identity),
            offset: PointerOffsetTerm::Constant(i64::MIN),
        };
        let mut identities = self
            .blocks
            .range(PointerBlock::Heap(0)..PointerBlock::Temporary(0))
            .filter_map(|(block, _)| match block {
                PointerBlock::Heap(identity) => Some(*identity),
                _ => None,
            })
            .chain(
                self.heap
                    .deallocated_allocations
                    .range(heap_base(0)..)
                    .map_while(|(base, _)| match base.block {
                        PointerBlock::Heap(identity) => Some(identity),
                        _ => None,
                    }),
            )
            .chain(
                self.heap
                    .pending_allocations
                    .keys()
                    .filter_map(|base| match base.block {
                        PointerBlock::Symbolic(variable) => Some(variable.0),
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
        let object_class = std::sync::Arc::make_mut(&mut self.heap)
            .pending_object_classes
            .remove(base);
        if succeeds {
            let mut block = CBlock::with_symbolic_size(bytes.clone());
            block.declared_class = object_class;
            std::sync::Arc::make_mut(&mut self.blocks).insert(resolved_base.block.clone(), block);
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
        self,
        variable: Variable,
        preserved_blocks: &dyn BlockMembership,
        mutable_ranges: Option<&[CMemoryRange]>,
        ledger: Option<&crate::kernel::loans::LoanLedger>,
    ) -> Self {
        self.with_loop_memory_havoc_preserving_frame(
            variable,
            preserved_blocks,
            mutable_ranges,
            ledger,
            None,
        )
    }

    pub(in crate::kernel) fn with_loop_memory_havoc_preserving_frame(
        mut self,
        variable: Variable,
        preserved_blocks: &dyn BlockMembership,
        mutable_ranges: Option<&[CMemoryRange]>,
        ledger: Option<&crate::kernel::loans::LoanLedger>,
        kept_by_function: Option<CallKeptRanges>,
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
        // Interned histories may share a variable and write footprint only
        // when they retain the same frame. The persistent frame identity is
        // already maintained; naming it does not enumerate its resources.
        let marker = kept_by_function.as_ref().map_or_else(
            || format!("havoc:{}", variable.0),
            |kept| format!("havoc:{}:{}", variable.0, kept.identity()),
        );
        std::sync::Arc::make_mut(&mut self.blocks).insert(
            marker.into(),
            CBlock::new(mutable_ranges.map_or(0, memory_havoc_write_set_fingerprint)),
        );
        if let Some(base) = base {
            record_c_memory_derivation(
                &mut self,
                CMemoryDerivation::LoopHavoc {
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
        preserved_blocks: &dyn BlockMembership,
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
        preserved_blocks: &dyn BlockMembership,
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
        preserved_blocks: &dyn BlockMembership,
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
        .map_err(|base| {
            format!("interface arms disagree on unwritten object extent at {base:?}")
        })?;

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
                if !preserved_blocks.contains_block(&pointer.block) {
                    record.record(pointer, value.byte_width());
                }
            }
            for ((pointer, c_type), _) in local_block_entries(&memory.union_cells) {
                visited += 1;
                if !preserved_blocks.contains_block(&pointer.block) {
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
        let candidates = call_havoc_candidates(mutable_ranges);
        // Cells and typed union views by one rule: a view is the
        // authoritative answer to an exact typed load, so one the callee may
        // have overwritten goes exactly as a cell does
        // (`mdtests/call_havoc_drops_a_union_member_view.md`). A callee can
        // only initialize more, so the automatic values that go stay
        // initialized.
        let selected = kept.map(|kept| {
            self.cells
                .call_unowned_candidates(&kept.residual, &candidates)
        });
        let scope = match selected.as_ref() {
            Some((selected, runs)) => ForgetScope::Ordered {
                candidates: &candidates,
                selected,
                runs: Some(runs),
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
            ask_every_slot,
        );
        let kept_ranges = call_havoc_kept_ranges(kept);
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
        // walks only the paths the two snapshots do not share.
        let candidates = call_havoc_candidates(mutable_ranges);
        let mut visited = 0usize;
        let mut dropped_cells = Vec::new();
        let mut dropped_initialized = Vec::new();
        let selected = kept.map(|kept| {
            before
                .cells
                .call_unowned_candidates(&kept.residual, &candidates)
        });
        let entries = before.cells.candidate_logical_entries_selected(
            &candidates,
            selected.as_ref().map(|(cells, _)| cells.as_slice()),
            selected.as_ref().map(|(_, runs)| runs.as_slice()),
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
            match call_havoc_keeps_cell(&key.0, value, mutable_ranges, assumptions, kept, true) {
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
        // a dropped value or the write set ([`CMemory::forget_cached_values`]).
        let mut expected = before.clone();
        expected.record_dropped_local_cells(&dropped_initialized);
        expected.forget_zero_readings_under(
            dropped_initialized
                .iter()
                .map(|(pointer, _)| &pointer.block),
        );
        expected.forget_zeroed_allocations_written_by(mutable_ranges, assumptions);
        if !self.heap.eq_relative_to(&expected.heap, &before.heap) {
            return false;
        }
        let kept_ranges = call_havoc_kept_ranges(kept);
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
        if base.block.is_local_block()
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
        if base.block.is_local_block()
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
        if base.block.is_local_block()
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
        if base.block.is_local_block()
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
            !source.pointer().block.is_local_block()
            || self.cells.runs_in_block(&source.pointer().block)
                .any(|run| !matches!(run.value_mode(), RunValueMode::Constant(_))));
        if !base.block.is_local_block() || snapshot_copy {
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
            pointer.block.is_local_block()
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
                && (!base.block.is_local_block()
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
                || (pointer.block.is_local_block()
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

    /// Observe and cache a scalar cell without changing its physical bytes.
    /// The observation is computed here so callers cannot supply a new value
    /// under the guise of a read.
    pub(crate) fn materialize_symbolic_cell(self, pointer: Pointer, c_type: CType) -> Self {
        let value = crate::kernel::eval::symbolic_storage_cell_value(&self, &pointer, c_type, true);
        match value {
            Some(value) => self.materialize_named_cell(pointer, value),
            None => self,
        }
    }

    /// Name one contract field at its selected source snapshot without
    /// recording a program write. The producer's source is shared by all
    /// fields of the same entry object; deriving the value here preserves
    /// that identity without accepting an arbitrary cached value.
    pub(crate) fn materialize_cell_from_source(
        self,
        pointer: Pointer,
        c_type: CType,
        source: SharedCMemory,
    ) -> Self {
        let kind = LoadKind::of_type(c_type).expect("contract fields have scalar read kinds");
        let load = crate::kernel::canonical_form_of_load(source, pointer.clone(), kind);
        let value = crate::kernel::cell_run_value(c_type, load);
        self.materialize_named_cell(pointer, value)
    }

    /// Cache the canonical value of an already existing cell for a resource
    /// projection. This is not a C write and cannot establish initialization.
    /// Kernel producers supply the value they observed or proved at this point.
    pub(in crate::kernel) fn materialize_named_cell(
        mut self,
        pointer: Pointer,
        value: CValue,
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
        if pointer.block.is_local_block() && self.has_block(&pointer.block) {
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
        std::sync::Arc::make_mut(&mut self.cells).insert(pointer, value);
        record_c_memory_derivation(&mut self, CMemoryDerivation::CellObserved { base });
        self
    }

    /// Writes one cell. The transition's fact context is not recorded on the
    /// store edge: a later load of another cell of the same base crosses the
    /// edge only with distinctness evidence checked in the querying context.
    pub fn store_with_context(
        self,
        pointer: Pointer,
        value: CValue,
        context: &PureFactContext,
    ) -> Self {
        self.store_with_effective_type(pointer, value, context, None)
    }

    /// [`Self::store_with_context`] for a C store through an lvalue of
    /// `class`, which also records the effective type it gives a heap cell
    /// (`design/effective-types.md`). Like the initialized bytes, the record
    /// changes with the cell under the one store edge, so the memory history
    /// stays connected.
    pub(in crate::kernel) fn store_classed_with_context(
        self,
        pointer: Pointer,
        value: CValue,
        context: &PureFactContext,
        class: Option<crate::kernel::effective_type::CAccessClass>,
    ) -> Self {
        self.store_with_effective_type(pointer, value, context, Some(class))
    }

    fn store_with_effective_type(
        mut self,
        pointer: Pointer,
        value: CValue,
        context: &PureFactContext,
        effective_type: Option<Option<crate::kernel::effective_type::CAccessClass>>,
    ) -> Self {
        crate::kernel::debug_assert_widths(
            "a stored value",
            || crate::kernel::value_mismatch(&value),
            &value,
        );
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
        if let Some(class) = effective_type
            && matches!(pointer.block, PointerBlock::Heap(_))
        {
            let mut record = self.heap.effective_types.clone();
            if record.record(&pointer, value.byte_width(), class, &value) {
                std::sync::Arc::make_mut(&mut self.heap).effective_types = record;
            }
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

    /// The integer terms held by the concrete cells this memory changed
    /// since `earlier`, or by every concrete cell when there is no earlier
    /// memory: what a recorded point newly names in memory. The walk visits
    /// only the changed cells of memories derived from one another.
    pub(crate) fn changed_cell_integers<'a>(
        &'a self,
        earlier: Option<&'a Self>,
    ) -> Vec<&'a Bitvector32Term> {
        self.cells
            .changed_concrete_cells(earlier.map(|earlier| earlier.cells.as_ref()))
            .into_iter()
            .filter_map(|(_, value)| match value.numeric_value() {
                CValue::Bool(term)
                | CValue::Int8(term)
                | CValue::Int16(term)
                | CValue::Int32(term)
                | CValue::UInt8(term)
                | CValue::UInt16(term)
                | CValue::UInt32(term)
                | CValue::Int64(term)
                | CValue::UInt64(term)
                | CValue::Int128(term)
                | CValue::UInt128(term) => Some(term),
                _ => None,
            })
            .collect()
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
    /// block holding it; a symbolic offset by the same spelling.
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
    /// [`Self::store_union_views`] keep the two disjoint at every pointer, so
    /// this answers `false` wherever [`Self::known_value`] answers `Some`; it is
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

    /// The pointer a typed union view records at exactly `pointer`, when one
    /// does: one key range, as [`Self::union_views_at`] reads it.
    pub(in crate::kernel) fn known_union_pointer(&self, pointer: &Pointer) -> Option<CValue> {
        self.union_views_at(pointer)
            .find(|(_, value)| matches!(value, CValue::Pointer(_)))
            .map(|(_, value)| value.clone())
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
    /// as initialized, where they are automatic storage: a store only ever
    /// initializes, so the bytes stay initialized with the value unknown.
    /// Heap cells need nothing here — a heap store records its bytes as it
    /// writes them. Costs the dropped cells.
    fn record_dropped_local_cells(&mut self, dropped: &[(Pointer, u32)]) {
        let mut record = self.heap.initialized.clone();
        let mut changed = false;
        for (pointer, width) in dropped {
            if pointer.block.is_local_block() {
                changed |= record.record(pointer, *width);
            }
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
    /// reading, and, in automatic storage, stays recorded initialized (a
    /// write only ever initializes). A new representation of cached bytes
    /// belongs in this function, so no transition can miss it.
    ///
    /// The slots `run_rule` drops as a whole run are recorded initialized
    /// where they are automatic ([`Self::record_dropped_local_run_slots`]),
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
                    runs,
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
        self.record_dropped_local_cells(&forgotten_cells);
        // A run's slots are cells too, dropped by `run_rule` as a whole run
        // without `fate` being asked; automatic ones stay initialized.
        self.record_dropped_local_run_slots(&dropped_run_slots);
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

    /// [`Self::record_dropped_local_cells`] for run slots dropped as a whole
    /// run. A dropped interval whose bytes the record already holds costs
    /// one covering query: the usual case, as a declaration's initializer,
    /// which is what makes a run of automatic storage, records its whole
    /// object ([`Self::with_initialized_object`]). Otherwise contiguous
    /// slots are one run of bytes, and only slots strided apart or at a
    /// symbolic offset are recorded one by one, each as a dropped cell.
    fn record_dropped_local_run_slots(&mut self, dropped: &[DroppedRunSlots]) {
        if dropped.is_empty() {
            return;
        }
        let mut record = self.heap.initialized.clone();
        let mut changed = false;
        for DroppedRunSlots { run, elements } in dropped {
            if !run.base().block.is_local_block() {
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

    /// Populate the derived cell partition while establishing function inputs,
    /// so the first field store pays only for its own cached cells.
    pub(crate) fn prepare_parameter_store_partition(&self, resources: &ResourceContext) {
        self.cells.prepare_parameter_partition(resources);
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
    /// `step_effect::cell_effect` and the snapshot comparisons conjoin it: the
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
        // `record_dropped_local_cells`), and ends a zero reading under it.
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
        // Objects a known address equality ties to the written one may share
        // the written bytes.
        let address_connected = assumptions.address_connected_objects(&normalized_pointer);
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
            if !address_connected.is_empty()
                && address_connected.contains(&crate::kernel::assumptions::parameter_alias_bucket(
                    &normalized_cell_pointer,
                ))
            {
                return if crate::kernel::memory_provenance::indexed_store_byte_separation_evidence(
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
            if !address_connected.is_empty()
                && address_connected.contains(&crate::kernel::assumptions::parameter_alias_bucket(
                    &normalized_cell_pointer,
                ))
            {
                return if crate::kernel::memory_provenance::indexed_store_byte_separation_evidence(
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
        let ordered = memory
            .cells
            .ordered_store_candidates(&normalized_pointer, bytes, &candidates, assumptions)
            .or_else(|| {
                memory.cells.parameter_store_candidates(
                    &normalized_pointer,
                    bytes,
                    &candidates,
                    &gap_kept,
                    assumptions,
                )
            })
            .or_else(|| {
                // A pointer value reaches no local whose address is never
                // taken (`never_address_taken_local_versus_pointer_value`),
                // so a store through one asks only the cells a pointer can
                // reach, unless a stated equality places it in such a local.
                (matches!(normalized_pointer.block, PointerBlock::Symbolic(_))
                    && !assumptions
                        .exact_pointer_aliases(&normalized_pointer)
                        .any(|alias| {
                            crate::kernel::primitives::block_is_never_address_taken_local(
                                &alias.block,
                            )
                        }))
                .then(|| memory.cells.pointer_reachable_cells())
            });
        let scope = match ordered.as_deref() {
            Some(selected) => ForgetScope::Ordered {
                candidates: &candidates,
                selected,
                runs: None,
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

    pub(crate) fn string_literal_pointer(function: &str, name: &str, bytes: &[u8]) -> Pointer {
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
                .any(|block| !block.is_local_block() && !block.is_havoc_block())
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
                .all(|change| blocks.contains_block(&change.key().0.block))
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
            LoadKind::Int32,
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
            LoadKind::UInt32,
        ))
    }

    pub(in crate::kernel) fn symbolic_int64_load(&self, pointer: &Pointer) -> CValue {
        CValue::Int64(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
            LoadKind::Bits64,
        ))
    }

    pub(in crate::kernel) fn symbolic_uint64_load(&self, pointer: &Pointer) -> CValue {
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

    /// [`Self::symbolic_pointer_load`] for a logical read: the pointer read
    /// is named by the cell's version ([`Pointer::version_read`]).
    pub(in crate::kernel) fn symbolic_pointer_version_load(
        &self,
        pointer: &Pointer,
        value_type: CType,
    ) -> CValue {
        let snapshot = crate::kernel::intern_c_memory(self.clone());
        // A version read is a named read, or a value the memory holds for the
        // cell, either of which already carries its definition.
        match Pointer::version_read_value(&snapshot, pointer) {
            Ok(held) => CValue::Pointer(held.with_type(value_type)),
            Err(value) => CValue::Pointer(CPointerValue::from_read(
                value, value_type, &snapshot, pointer,
            )),
        }
    }

    pub(in crate::kernel) fn symbolic_pointer_load(
        &self,
        pointer: &Pointer,
        value_type: CType,
    ) -> CValue {
        let snapshot = crate::kernel::intern_c_memory(self.clone());
        let value = Pointer::loaded(&Bitvector32Term::MemoryLoad(
            snapshot.clone(),
            Box::new(pointer.clone()),
            LoadKind::Int32,
        ))
        .expect("a memory load names its read");
        // This factory constructs an exact typed read, just like the seeded
        // cell producer. Keep its defining snapshot and address even when a
        // resource argument evaluator does not retain a C load's fact stream.
        crate::kernel::equality_graph::EqualityGraph::default()
            .register_pointer_read_definition(&value, &snapshot, pointer);
        CValue::Pointer(CPointerValue::from_read(
            value, value_type, &snapshot, pointer,
        ))
    }
}

impl CState {
    /// The first part of `self` that differs from `other`, named for a
    /// diagnostic, or `None` when the states are equal. A differing resource
    /// context names a resource fact held on one side only; every other part
    /// is named by what it is.
    pub(crate) fn first_difference(&self, other: &CState) -> Option<String> {
        if self.resources != other.resources {
            let only_in = |left: &ResourceContext, right: &ResourceContext| {
                left.facts()
                    .iter()
                    .find(|fact| !right.facts().contains(fact))
                    .map(CResourceFact::diagnostic_summary)
            };
            return Some(match only_in(&self.resources, &other.resources) {
                Some(fact) => format!("`{fact}` is held only before the rewrite"),
                None => match only_in(&other.resources, &self.resources) {
                    Some(fact) => format!("`{fact}` is held only in the published state"),
                    None => "the resource facts are held in a different representation".to_string(),
                },
            });
        }
        let parts: [(&str, bool); 22] = [
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
                "the aggregate destination",
                self.aggregate_destination != other.aggregate_destination,
            ),
            ("the loan ledger", self.loan_ledger != other.loan_ledger),
            (
                "the loan participant",
                self.loan_participant != other.loan_participant,
            ),
            (
                "the loan view bindings",
                self.loan_view_bindings != other.loan_view_bindings,
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
        fn same_or_empty_persistent_map<K: Ord, V>(
            left: &crate::persistent::PersistentMap<K, V>,
            right: &crate::persistent::PersistentMap<K, V>,
        ) -> bool {
            left.shares_root_with(right) || (left.is_empty() && right.is_empty())
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
            && same_bindings
            && same_or_empty_persistent_map(&self.locals.bindings, &other.locals.bindings)
            && same_or_empty_persistent_map(&self.locals.slots, &other.locals.slots)
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
            .map_err(|refusal| format!("opaque population import refused: {refusal}"))?;
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
                .map_err(|refusal| format!("named authority import refused: {refusal}"))?;
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
            .map_err(|refusal| format!("batch population import refused: {refusal}"))?;
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
            .map_err(|refusal| format!("wildcard population import refused: {refusal}"))?;
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
            .map_err(|refusal| format!("wildcard authority import refused: {refusal}"))?;
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
            .map_err(|error| format!("control body ownership refused: {error}"))?;
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
            let external = is_external_population_anchor(anchor);
            let count = if !external && anchor.offset == PointerOffsetTerm::Constant(0) {
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
            .map_err(|error| {
                format!(
                    "could not evaluate the acquired control authority: {}",
                    crate::kernel::api::describe_certification_runtime_error(&error)
                )
            })?;
            let CResource::PopulationAuthority(description) = authority.resource() else {
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
                    LoadKind::Int32,
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
                    .map_err(|error| format!("control authority evaluation failed: {error}"))?
                    .map_err(|error| format!("control authority evaluation failed: {error}"))?
                }
                super::super::CResourceTerm::Memory(_) => {
                    // The held control's body, as its fold established it
                    // (`assume_entry_clause_extents`).
                    super::super::functions::evaluate_function_resource_spec(
                        &evaluation,
                        spec,
                        &assumptions.clone().assume_entry_clause_extents(),
                        &mut budget,
                    )
                    .map_err(|error| format!("control memory evaluation failed: {error}"))?
                    .map_err(|error| format!("control memory evaluation failed: {error}"))?
                }
                super::super::CResourceTerm::Token { name, .. }
                    if name == CResourceFact::ALLOCATION_RESOURCE_NAME =>
                {
                    // The held control's body, as its fold established it
                    // (`assume_entry_clause_extents`).
                    super::super::functions::evaluate_function_resource_spec(
                        &evaluation,
                        spec,
                        &assumptions.clone().assume_entry_clause_extents(),
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
                || pointer.block.is_local_block() && self.memory.has_block(&pointer.block))
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
            && (anchor.offset != PointerOffsetTerm::Constant(0)
                || !(matches!(&anchor.block, PointerBlock::Heap(_))
                    && self.memory.live_heap_block_size(anchor).is_some()
                    || anchor.block.is_local_block() && self.memory.has_block(&anchor.block)))
        {
            return Err("Requires live base storage for authority(R(p))".into());
        }
        let mut next = self.clone();
        let evidence = if establish {
            let (history, evidence) = events
                .checked_establish(&anchor.block, description)
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
                events.checked_retire(&anchor.block, description)
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
                    || anchor.block.is_local_block() && self.memory.has_block(&anchor.block)))
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
            // Birth checks the supplied body's storage. On death the owned
            // member is the evidence: consuming it below returns that same
            // body. Do not rediscover its introduction premises from the
            // current ambient loadability facts.
            if produce
                && !imported_member_exchange
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
                .map_err(|error| format!("member ownership refused: {error}"))?
        } else {
            let resources = self
                .resources
                .clone()
                .without_fact_incrementally(selected, assumptions)
                .ok_or_else(|| format!("Requires owns {name}(p)"))?;
            resources
                .try_compose_with_facts_delaying_normalization(body.iter().cloned(), assumptions)
                .map_err(|error| format!("member body ownership refused: {error}"))?
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
                    .map_err(|refusal| format!("named member change refused: {refusal}"))?
            } else {
                events
                    .checked_instance_exchange(&reference, produce)
                    .map_err(|refusal| format!("named member change refused: {refusal}"))?
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
        blocks: &[PointerBlock],
    ) -> Result<Option<super::super::population_authority::c_creation::CreationEvents>, CRuntimeError>
    {
        let Some(mut events) = self.population_effects.creation.clone() else {
            return Ok(None);
        };
        for block in blocks {
            events = events.retired(block).map_err(|refusal| {
                CRuntimeError::FunctionContract(format!(
                    "population authority prevents storage retirement: {refusal}"
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
                    "population authority prevents storage retirement: {refusal}"
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
        // The candidates are the scalar locals bound to the variable, found
        // through the held-term index; each must still hold it in current
        // memory at its slot's start. The first such slot answers.
        let term = Bitvector32Term::Variable(variable);
        let mut held = None;
        for name in self.locals.names_holding_integer(&term) {
            if crate::instrumentation::deadline_exceeded() {
                return None;
            }
            let Some(pointer) = self.locals.slot(name) else {
                continue;
            };
            if pointer.offset == PointerOffsetTerm::Constant(0)
                && self.memory.cells.bitvector_variable_at(pointer) == Some(variable)
                && held.is_none_or(|(first, _): (&Pointer, &str)| pointer < first)
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
        pointer: &Pointer,
    ) -> Option<&str> {
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
                // A store through a pointer to the other signedness of the
                // object's width wrote the same bits; the local reads them in
                // its own type (`CType::read_cell`).
                memory
                    .known_value(&slot)
                    .and_then(|value| {
                        c_type.read_cell(&value).or_else(|| {
                            (!matches!(binding, CLocalBinding::UninitializedObject { .. }))
                                .then_some(value)
                        })
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
/// `crate::languages::c::address_taken::summarize_address_taken`.
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
mod interface_join_tombstone_tests {
    use super::*;

    /// A join retains a tombstone if any incoming arm freed the allocation,
    /// even when another arm still lists it as potentially live. A later
    /// dereference through the alias must be rejected until the paths are
    /// distinguished.
    #[test]
    fn interface_join_keeps_one_arm_deallocation() {
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
        runs: Option<&'a [cell_store::RunKey]>,
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

/// Collects one dropped cell for [`CMemory::record_dropped_local_cells`],
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
        .take_while(|(key, _)| key.key_block().is_local_block())
}

#[cfg(test)]
mod initialization_record_tests {
    use super::*;

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

    fn scalar(state: CState, name: &str, value: CValue) -> CState {
        let memory = state
            .memory()
            .clone()
            .store(CMemory::local_pointer(name), value.clone());
        state.with_local(name, value).with_memory(memory)
    }

    #[test]
    fn pointer_object_index_tracks_rebindings_and_scope_changes() {
        let blocks = [
            PointerBlock::Symbolic(Variable(971_030)),
            PointerBlock::Symbolic(Variable(971_031)),
        ];
        let mut locals = CLocalEnvironment::new();
        for step in 0..60usize {
            let name = format!("p{}", step % 7);
            if step % 5 == 0 {
                locals.remove(&name);
            } else if step % 5 == 1 {
                locals.set(&name, int32(7));
            } else {
                locals.set(
                    &name,
                    CValue::pointer(Pointer {
                        block: blocks[step % 2].clone(),
                        offset: PointerOffsetTerm::Constant(step as i64),
                    }),
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
                CLocalEnvironment::from_parts(locals.bindings.clone(), locals.slots.clone());
            for block in &blocks {
                let scanned = locals
                    .object_values()
                    .filter_map(|(name, value)| match value {
                        CValue::Pointer(p) if &p.block == block => Some((name, p)),
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                for indexed in [&locals, &saved, &rebuilt] {
                    assert_eq!(
                        indexed.pointer_objects_in_block(block).collect::<Vec<_>>(),
                        scanned
                    );
                }
            }
        }
    }

    #[test]
    fn held_term_index_agrees_with_a_scan_of_the_bindings() {
        let x = Bitvector32Term::Variable(Variable(971_020));
        let y = Bitvector32Term::Variable(Variable(971_021));
        // Terms that share a fingerprint (same root and operand roots) but
        // differ deeper, beside equal terms held by several locals.
        let deep = |term: Bitvector32Term| {
            binary_node!(
                Int32,
                Add,
                Box::new(binary_node!(
                    Int32,
                    Add,
                    Box::new(term),
                    Box::new(x.clone())
                )),
                Box::new(Bitvector32Term::Constant(1)),
            )
        };
        let terms = [
            x.clone(),
            y.clone(),
            deep(x.clone()),
            deep(y.clone()),
            Bitvector32Term::Constant(7),
        ];
        let mut state = CState::new();
        for step in 0..60usize {
            let name = format!("v{}", step % 13);
            if step % 7 == 6 {
                state.locals.remove(&name);
            } else {
                let term = terms[step % terms.len()].clone();
                state = state.with_local(name, CValue::Int32(term));
            }
        }
        state = state.with_local("pointer", CValue::pointer(CMemory::local_pointer("v0")));
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

    fn held_integer_term_of(value: &CValue) -> Option<&Bitvector32Term> {
        match value.numeric_value() {
            crate::kernel::integer_c_value!(term) | CValue::Bool(term) => Some(term),
            _ => None,
        }
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

    fn ranges(id: u64) -> SnapshotMap<CMemoryRange, ()> {
        ResourceContext::new()
            .unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
                Pointer::symbolic(Variable(id)),
                0.into(),
                4.into(),
            )))
            .flat_owned_memory_ranges()
            .clone()
    }

    #[test]
    fn kept_range_hash_collisions_use_exact_sets_across_threads() {
        let first = intern_kept_range_set_with_hash(ranges(7), SnapshotMap::new(), 0);
        let same = intern_kept_range_set_with_hash(ranges(7), SnapshotMap::new(), 0);
        let different = intern_kept_range_set_with_hash(ranges(8), SnapshotMap::new(), 0);
        assert_eq!(first.id, same.id);
        assert_ne!(first.id, different.id);
        let across = std::thread::spawn(|| {
            intern_kept_range_set_with_hash(ranges(7), SnapshotMap::new(), 0)
        })
        .join()
        .unwrap();
        assert_eq!(first.id, across.id);
    }

    #[test]
    fn kept_range_hash_collisions_distinguish_composite_exclusions() {
        let composite = ResourceContext::new().unchecked_with_fact(CResourceFact::own_composite(
            "boxed".into(),
            vec![CValue::pointer(Pointer::symbolic(Variable(9)))],
        ));
        let intern = |original, introduced| {
            intern_kept_range_set_with_exclusions_and_hash(
                ranges(7),
                SnapshotMap::new(),
                original,
                introduced,
                SnapshotMap::new(),
                0,
            )
        };
        let original = ResourceContext::new()
            .unchecked_with_facts(ranges(8).keys().cloned().map(CResourceFact::own_memory));
        let original = original.memory_input_facts();
        let plain = intern(SnapshotMap::new(), SnapshotMap::new());
        let excluded = intern(original.clone(), SnapshotMap::new());
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
        let viewed = ResourceContext::new().unchecked_with_fact(CResourceFact::view_memory(range));
        let intern = |inputs| {
            intern_kept_range_set_with_exclusions_and_hash(
                SnapshotMap::new(),
                SnapshotMap::new(),
                SnapshotMap::new(),
                SnapshotMap::new(),
                inputs,
                0,
            )
        };
        let empty = intern(SnapshotMap::new());
        let kept = intern(viewed.memory_input_facts().clone());
        assert_ne!(empty.id, kept.id);
        assert_eq!(kept.id, intern(viewed.memory_input_facts().clone()).id);
    }

    #[test]
    fn owned_range_index_keeps_duplicates_until_the_last_withdrawal() {
        let fact = CResourceFact::own_memory(CMemoryRange::new(
            Pointer::symbolic(Variable(7)),
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
