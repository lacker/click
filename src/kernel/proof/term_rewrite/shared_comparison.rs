//! Shared machine reconstruction for checking and scoped rewriting.
//! This is not lowering: stored operands keep their exact syntax.
use super::*;

thread_local! {
    static BINARY_RESULTS: std::cell::RefCell<HashMap<(MachineIntegerType, MachineBinaryOp, u64, u64), KernelTerm>> = Default::default();
    static COMPARISON_OPERANDS: std::cell::RefCell<HashMap<u64, KernelTerm>> = Default::default();
}

pub(super) fn clear() {
    BINARY_RESULTS.with(|cache| cache.borrow_mut().clear());
    COMPARISON_OPERANDS.with(|cache| cache.borrow_mut().clear());
}

impl TermRewrite<'_> {
    /// Checking-only reconstruction shared with arithmetic comparison. The
    /// operands stay in the shared arena; syntax work uses the same memo.
    pub(in crate::kernel) fn machine_binary_reading(
        format: MachineIntegerType,
        op: MachineBinaryOp,
        left: KernelTerm,
        right: KernelTerm,
    ) -> KernelTerm {
        comparison_binary(format, op, left, right)
    }

    /// Reconstruct shared arithmetic, including Integer conversion leaves.
    /// Comparison mode simplifies arithmetic; substitution preserves raw
    /// operators, and exact Integer congruence also preserves raw casts.
    /// Only comparison results cross queries.
    /// Native opaque replacements remain exact leaves beneath shared parents.
    pub(in crate::kernel) fn shared_machine_operand(
        &mut self,
        root: &KernelTerm,
    ) -> Option<KernelTerm> {
        // Only the ordinary comparison scope may share work between queries.
        // A nested binder's renamed/opaque reads use this traversal's own memo.
        let cacheable = self.conditions.is_none()
            && self.comparison_arithmetic
            && self.resolve_registered_loads
            && self.scope.program_values.iter().all(|(a, b)| a == b)
            && self.scope.integer.iter().all(|(a, b)| a == b)
            && self.scope.algebraic.iter().all(|(a, b)| a == b);
        let local = std::cell::RefCell::new(HashMap::<u64, KernelTerm>::new());
        let shared_cache = self
            .shared_machine_cache
            .get_or_insert_with(Default::default)
            .clone();
        let scope_id = self.scope_id;
        let source_disabled = self.source_disabled;
        let integer_shadowed = self.integer_shadowed;
        let resolve_reads = self.resolve_registered_loads;
        let key = |term: &KernelTerm| {
            (
                term.id(),
                scope_id,
                source_disabled,
                integer_shadowed,
                resolve_reads,
            )
        };
        let get = |term: &KernelTerm| {
            local
                .borrow()
                .get(&term.id())
                .cloned()
                .or_else(|| shared_cache.borrow().get(&key(term)).cloned())
                .or_else(|| {
                    cacheable
                        .then(|| {
                            COMPARISON_OPERANDS
                                .with(|cache| cache.borrow().get(&term.id()).cloned())
                        })
                        .flatten()
                })
        };
        let mut sources = HashMap::<MachineIntegerType, Option<KernelTerm>>::new();
        let mut opaque_sources = self
            .bitvector
            .map(|(from, _)| super::super::machine_source_match::MachineSourceMatcher::new(from));
        let mut replacements = HashMap::<MachineIntegerType, KernelTerm>::new();
        let mut guards = HashMap::<u64, (ConditionTerm, KernelTerm)>::new();
        let mut pending = vec![(root.clone(), false)];
        while let Some((term, finish)) = pending.pop() {
            self.visit();
            if self.checked_work_exhausted() {
                return None;
            }
            if get(&term).is_some() {
                continue;
            }
            if self.conditions.is_some()
                && !self.comparison_arithmetic
                && self.bitvector.is_none()
                && self.integer_exact.is_none()
                && self.integer_variables.is_none()
                && self.typed_variables.is_none()
                && !self.resolve_registered_loads
                && self.scope.program_values.is_empty()
                && self.scope.integer.is_empty()
                && self.scope.algebraic.is_empty()
                && !term.has_conditional_machine_rewrites()
            {
                local.borrow_mut().insert(term.id(), term.clone());
                continue;
            }
            let KernelType::Program(ty) = term.ty() else {
                return None;
            };
            let format = MachineIntegerType::from_program_type(*ty)?;
            // Exact machine replacement precedes descent, as in `bits`.
            // Import each selected source/replacement once per interpretation,
            // rather than rebuilding it at every shared occurrence.
            if !self.source_disabled
                && let Some((from, to)) = self.bitvector
                && (from.variable().is_none()
                    || from.variable().is_some_and(crate::kernel::is_load_variable)
                    || matches!(to, MachineOperandView::Shared(_)))
                && !from
                    .variable()
                    .is_some_and(|variable| self.scope.program_values.contains_key(variable))
            {
                let source = sources.entry(format).or_insert_with(|| match from {
                    MachineOperandView::Legacy(from) => {
                        KernelTermImport::default().machine_arithmetic(format, from)
                    }
                    MachineOperandView::Shared(from) => {
                        Some(from.with_machine_observation_type(format))
                    }
                });
                let mut matches = source.as_ref() == Some(&term);
                if !matches
                    && root.has_machine_conversions()
                    && (source.is_none()
                        || source.as_ref().is_some_and(KernelTerm::has_machine_matches)
                        || matches!(from, MachineOperandView::Shared(value) if value.has_machine_conversions()))
                {
                    let Some(found) = opaque_sources
                        .as_mut()
                        .expect("selected source")
                        .matches(format, &term)
                    else {
                        self.integer_work_exhausted = true;
                        return None;
                    };
                    matches = found;
                }
                if matches {
                    let replacement = replacements
                        .entry(format)
                        .or_insert_with(|| KernelTerm::retained_machine_operand(format, to))
                        .clone();
                    if crate::instrumentation::deadline_exceeded_with_work(0) {
                        self.integer_work_exhausted = true;
                        return None;
                    }
                    self.changed = true;
                    local.borrow_mut().insert(term.id(), replacement);
                    continue;
                }
            }
            if !finish && let KernelTermNode::MachineIf { arguments } = term.node() {
                let condition = KernelTermExport::condition(&arguments[0]).ok()?;
                if let Some(collected) = &mut self.collected_conditions {
                    collected.push(condition.clone());
                }
                let original = condition;
                let condition = self.condition(&original);
                let condition = if self.integer_exact.is_some() {
                    condition
                } else {
                    folded_machine_condition(condition)
                };
                let guard = if condition == original {
                    arguments[0].clone()
                } else {
                    KernelTermImport::default().condition(&condition)
                };
                guards.insert(term.id(), (condition, guard));
            }
            let children: Vec<_> = match term.node() {
                KernelTermNode::MachineIf { arguments } => match guards.get(&term.id()) {
                    Some((ConditionTerm::Constant(value), _)) if self.integer_exact.is_none() => {
                        vec![arguments[if *value { 1 } else { 2 }].clone()]
                    }
                    _ => arguments[1..].to_vec(),
                },
                KernelTermNode::MachineBinary { arguments, .. } => arguments.to_vec(),
                KernelTermNode::MachineUnary { operand, .. }
                | KernelTermNode::MachineCast { operand, .. } => vec![operand.clone()],
                _ => Vec::new(),
            };
            if !finish && !children.is_empty() {
                pending.push((term.clone(), true));
                pending.extend(children.into_iter().rev().map(|child| (child, false)));
                continue;
            }
            let value = match term.node() {
                KernelTermNode::Match(matched) => self
                    .rewrite_retained_match_value_in(matched)?
                    .with_machine_observation_type(format),
                KernelTermNode::Fold(fold) => self
                    .retained_fold_in(fold)
                    .ok()?
                    .into_term()
                    .with_machine_observation_type(format),
                KernelTermNode::MachineIf { arguments } => {
                    let (condition, guard) = guards.remove(&term.id()).expect("visited guard");
                    if self.integer_exact.is_none()
                        && let ConditionTerm::Constant(value) = condition
                    {
                        get(&arguments[if value { 1 } else { 2 }])?
                    } else {
                        let left = get(&arguments[1])?;
                        let right = get(&arguments[2])?;
                        if self.integer_exact.is_none()
                            && crate::kernel::shared_machine_syntax_equal(&left, &right)
                        {
                            left
                        } else {
                            KernelTerm::machine_if_shared(format, [guard, left, right])
                        }
                    }
                }
                KernelTermNode::Variable(variable) => {
                    let rewritten = self.bits(&MachineTerm::Variable(*variable));
                    KernelTerm::retained_machine_operand(
                        format,
                        MachineOperandView::Legacy(&rewritten),
                    )
                }
                KernelTermNode::MemoryLoad { .. } => {
                    let read = term.machine_read_leaf().expect("read leaf");
                    // The selected read owns its state; rewrite its address
                    // directly without manufacturing a reserved variable.
                    let rewritten = self.bits(read);
                    KernelTerm::retained_machine_operand(
                        format,
                        MachineOperandView::Legacy(&rewritten),
                    )
                }
                KernelTermNode::MachineLiteral(_) => term.clone(),
                KernelTermNode::Legacy(_)
                | KernelTermNode::Call { .. }
                | KernelTermNode::PointerAddress { .. } => {
                    let original = term
                        .machine_conversion_leaf()
                        .expect("retained native operand");
                    let value = self.bits(original);
                    term.rewritten_machine_leaf(format, original, &value)
                }
                KernelTermNode::IntegerToMachine { .. } | KernelTermNode::BoolCast { .. } => {
                    let value = self.bits(term.machine_conversion_leaf().expect("conversion leaf"));
                    KernelTerm::retained_machine_operand(format, MachineOperandView::Legacy(&value))
                }
                KernelTermNode::MachineBinary {
                    format: operation_format,
                    operator,
                    arguments,
                } => {
                    let [left, right] = arguments
                        .each_ref()
                        .map(|arg| get(arg).expect("visited operand"));
                    if self.comparison_arithmetic {
                        comparison_binary(*operation_format, *operator, left, right)
                    } else if self.conditions.is_some()
                        && let (Some(a), Some(b)) = (literal(&left), literal(&right))
                    {
                        // Selected conditions can turn opaque If operands into
                        // literals. Fold only those fixed-size children, as the
                        // native conditional rewriter does; retain symbolic DAGs.
                        let folded =
                            MachineTerm::machine_binary(*operation_format, *operator, a, b);
                        // The root may be a signed word-equality reading of an
                        // unsigned operation. Interpret a folded word in that
                        // root's format before observing its mathematical value.
                        let folded =
                            MachineTerm::machine_integer_cast(*operation_format, format, folded);
                        imported(format, folded)
                    } else {
                        KernelTerm::machine_binary_shared(
                            *operation_format,
                            *operator,
                            [left, right],
                        )
                    }
                }
                KernelTermNode::MachineUnary {
                    format,
                    operator,
                    operand,
                } => {
                    let operand = get(operand).expect("visited operand");
                    let operand = if self.comparison_arithmetic
                        && matches!(
                            format,
                            MachineIntegerType::Int32 | MachineIntegerType::UInt32
                        )
                        && let Some(value) = literal(&operand)
                    {
                        imported(*format, value.constant_word32())
                    } else {
                        operand
                    };
                    KernelTerm::machine_unary_shared(*format, *operator, operand)
                }
                KernelTermNode::MachineCast {
                    encoding,
                    source,
                    destination,
                    operand,
                } => {
                    let operand = get(operand).expect("visited operand");
                    if self.integer_exact.is_some() {
                        KernelTerm::machine_cast_shared(*encoding, *source, *destination, operand)
                    } else if *encoding == MachineCastSpelling::Generic {
                        self.widened_narrowed_shared_carrier(
                            match term.node() {
                                KernelTermNode::MachineCast { operand, .. } => operand,
                                _ => unreachable!(),
                            },
                            &operand,
                            *source,
                            *destination,
                        )
                        .unwrap_or_else(|| {
                            operand
                                .checking_machine_cast_preserving_sign_pairs(*source, *destination)
                        })
                    } else if encoding.unary(*source, *destination).is_width_conversion() {
                        operand.checking_legacy_machine_conversion(*source, *destination)
                    } else {
                        KernelTerm::machine_cast_shared(*encoding, *source, *destination, operand)
                    }
                }
                _ => return None,
            }
            .with_machine_observation_type(format);
            let value = self.reduce_shared_remainder(value);
            if crate::instrumentation::deadline_exceeded_with_work(0) {
                self.integer_work_exhausted = true;
            }
            if self.refusal().is_some() {
                return None;
            }
            local.borrow_mut().insert(term.id(), value.clone());
            shared_cache.borrow_mut().insert(key(&term), value.clone());
            if cacheable {
                COMPARISON_OPERANDS.with(|cache| cache.borrow_mut().insert(term.id(), value));
            }
        }
        get(root)
    }
}

impl TermRewrite<'_> {
    fn shared_guard_holds(&self, guard: &ConditionTerm) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        self.conditions
            .is_some_and(|conditions| conditions.get(guard) == Some(&true))
            || self
                .cited_comparison_context
                .is_some_and(|context| context.selected_comparison_value(guard) == Some(true))
            || folded_machine_condition(guard.clone()) == ConditionTerm::Constant(true)
    }

    fn widened_narrowed_shared_carrier(
        &mut self,
        original: &KernelTerm,
        rewritten: &KernelTerm,
        source: MachineIntegerType,
        destination: MachineIntegerType,
    ) -> Option<KernelTerm> {
        if (self.conditions.is_none() && self.collected_conditions.is_none())
            || !crate::kernel::is_narrow_widening32(source, destination)
        {
            return None;
        }
        let (MachineCastSpelling::Generic, original_source, original_destination, original) =
            MachineOperandView::Shared(original).cast()?
        else {
            return None;
        };
        let (MachineCastSpelling::Generic, rewritten_source, rewritten_destination, rewritten) =
            MachineOperandView::Shared(rewritten).cast()?
        else {
            return None;
        };
        if original_source != rewritten_source
            || original_destination != source
            || rewritten_destination != source
        {
            return None;
        }
        let MachineOperandView::Shared(original) = original else {
            unreachable!()
        };
        let MachineOperandView::Shared(rewritten) = rewritten else {
            unreachable!()
        };
        let (original_bounds, _) =
            shared_narrowed_cast_identity(original, original_source, source)?;
        let (bounds, carrier) = shared_narrowed_cast_identity(rewritten, rewritten_source, source)?;
        if let Some(collected) = &mut self.collected_conditions {
            collected.extend(original_bounds.into_iter().flatten());
            collected.extend(bounds.into_iter().flatten());
            return None;
        }
        self.conditions?;
        bounds
            .iter()
            .zip(&original_bounds)
            .all(|(a, b)| {
                a.iter()
                    .chain(b)
                    .any(|guard| self.shared_guard_holds(guard))
            })
            .then_some(carrier)
    }

    fn reduce_shared_remainder(&mut self, value: KernelTerm) -> KernelTerm {
        if self.conditions.is_none() && self.collected_conditions.is_none() {
            return value;
        }
        let Some((guards, replacement)) = shared_remainder_rewrite(&value) else {
            return value;
        };
        if let Some(collected) = &mut self.collected_conditions {
            collected.extend(guards.iter().cloned());
        }
        if self.conditions.is_some() && guards.iter().all(|guard| self.shared_guard_holds(guard)) {
            replacement
        } else {
            value
        }
    }
}

fn shared_narrowed_cast_identity(
    value: &KernelTerm,
    source: MachineIntegerType,
    destination: MachineIntegerType,
) -> Option<(Vec<Vec<ConditionTerm>>, KernelTerm)> {
    use crate::kernel::machine_integer::comparison::condition_for_operand_views;
    use MachineIntegerType as T;
    use MachineOperandView as V;
    if let Some(literal) = literal(value) {
        let (bounds, carrier) =
            crate::kernel::assumptions::narrowed_cast_identity(&literal, source, destination)?;
        return Some((
            bounds.into_iter().map(|b| b.conditions).collect(),
            imported(T::Int32, carrier),
        ));
    }
    let bits = destination.format().bits();
    let source_bits = source.format().bits();
    if !matches!(bits, 8 | 16) || destination.format().contains(source.format()) || source_bits > 64
    {
        return None;
    }
    let (lo, hi) = if destination.format().is_signed() {
        (-(1i64 << (bits - 1)), (1i64 << (bits - 1)) - 1)
    } else {
        (0, (1i64 << bits) - 1)
    };
    let source_signed = source.format().is_signed();
    let needs_lower = source_signed && -(1i128 << (source_bits - 1)) < i128::from(lo);
    let max = if source_signed {
        (1i128 << (source_bits - 1)) - 1
    } else {
        (1i128 << source_bits) - 1
    };
    let value = if source_bits < 32 {
        value.checking_machine_cast_preserving_sign_pairs(source, T::Int32)
    } else {
        value.clone()
    };
    let compare = |format, relation, bound: i64| {
        let bound = match format {
            T::Int64 => MachineTerm::int64_constant(bound),
            T::UInt64 => MachineTerm::uint64_constant(bound as u64),
            _ => MachineTerm::constant(bound as i32 as u32),
        };
        condition_for_operand_views(format, relation, [V::Shared(&value), V::Legacy(&bound)])
    };
    let format = match source {
        T::Int8 | T::UInt8 | T::Int16 | T::UInt16 => T::Int32,
        _ => source,
    };
    let mut bounds = Vec::new();
    if needs_lower {
        bounds.push(vec![compare(format, CompareRelation::GreaterEqual, lo)]);
    }
    if max > i128::from(hi) {
        let mut upper = vec![compare(format, CompareRelation::LessEqual, hi)];
        if matches!(source, T::UInt8 | T::UInt16) {
            upper.push(compare(T::UInt32, CompareRelation::LessEqual, hi));
        }
        bounds.push(upper);
    }
    let carrier = if source_bits == 64 {
        value.checking_legacy_machine_conversion(source, T::UInt32)
    } else {
        value
    };
    Some((bounds, carrier))
}

fn shared_remainder_rewrite(value: &KernelTerm) -> Option<(Vec<ConditionTerm>, KernelTerm)> {
    use crate::kernel::machine_integer::comparison::condition_for_operand_views;
    use MachineBinaryOp as O;
    use MachineIntegerType as T;
    use MachineOperandView as V;
    let KernelTermNode::MachineBinary {
        format,
        operator: O::Remainder,
        arguments: [n, d],
    } = value.node()
    else {
        return None;
    };
    let compare = |ty, relation, a: &KernelTerm, b: &KernelTerm| {
        let condition = condition_for_operand_views(ty, relation, [V::Shared(a), V::Shared(b)]);
        crate::kernel::assumptions::observation_comparisons::constant_observation_value(&condition)
            .map(ConditionTerm::Constant)
            .unwrap_or(condition)
    };
    if *format == T::UInt64 {
        let divisor = V::Shared(d).uint64_constant();
        if divisor == Some(1) {
            return Some((vec![], constant(*format, 0)));
        }
        if divisor.is_some_and(|d| d != 0)
            && let Some([original, tail]) = binary(n, *format, O::Subtract)
        {
            if let Some([tail_original, tail_d]) = binary(tail, *format, O::Remainder)
                && original == tail_original
                && d == tail_d
            {
                return Some((vec![], constant(*format, 0)));
            }
            if tail == d {
                return Some((
                    vec![compare(*format, CompareRelation::LessEqual, d, original)],
                    comparison_binary(*format, O::Remainder, original.clone(), d.clone()),
                ));
            }
        }
        return Some((
            vec![compare(*format, CompareRelation::LessThan, n, d)],
            n.clone(),
        ));
    }
    if *format != T::Int32 {
        return None;
    }
    let divisor = word(d)? as i32;
    if divisor == 1 {
        return Some((vec![], constant(*format, 0)));
    }
    if divisor <= 0 {
        return None;
    }
    let low = match n.node() {
        KernelTermNode::MachineCast {
            encoding: MachineCastSpelling::Generic,
            source: T::UInt32,
            destination: T::Int32,
            operand,
        } => operand,
        _ => n,
    };
    if let KernelTermNode::MachineCast {
        encoding: MachineCastSpelling::UInt32From64,
        operand: wide,
        ..
    } = low.node()
        && let Some([original, tail]) = binary(wide, T::UInt64, O::Subtract)
        && let Some([other_original, other_d]) = binary(tail, T::UInt64, O::Remainder)
        && original == other_original
        && V::Shared(other_d).uint64_constant() == Some(divisor as u64)
    {
        return Some((
            vec![compare(
                T::UInt64,
                CompareRelation::LessEqual,
                original,
                &constant(T::UInt64, i32::MAX as u32),
            )],
            constant(*format, 0),
        ));
    }
    if let Some([original, step]) = binary(n, T::Int32, O::Subtract)
        && step == d
    {
        return Some((
            vec![compare(*format, CompareRelation::LessEqual, d, original)],
            comparison_binary(*format, O::Remainder, original.clone(), d.clone()),
        ));
    }
    Some((
        vec![
            compare(
                *format,
                CompareRelation::LessEqual,
                &constant(*format, 0),
                n,
            ),
            compare(*format, CompareRelation::LessThan, n, d),
        ],
        n.clone(),
    ))
}

pub(super) fn literal(term: &KernelTerm) -> Option<MachineTerm> {
    MachineOperandView::Shared(term).literal()
}
pub(super) fn imported(format: MachineIntegerType, value: MachineTerm) -> KernelTerm {
    KernelTermImport::default()
        .machine_arithmetic(format, &value)
        .expect("machine arithmetic result")
}
fn constant(format: MachineIntegerType, value: u32) -> KernelTerm {
    imported(
        format,
        crate::kernel::machine_integer::range::constant_word(format, &value.into())
            .expect("small constant"),
    )
}
fn word(term: &KernelTerm) -> Option<u32> {
    literal(term)?.as_const()
}
pub(super) fn binary<'a>(
    term: &'a KernelTerm,
    format: MachineIntegerType,
    op: MachineBinaryOp,
) -> Option<&'a [KernelTerm; 2]> {
    match term.node() {
        KernelTermNode::MachineBinary {
            format: found,
            operator,
            arguments,
        } if *found == format && *operator == op => Some(arguments),
        _ => None,
    }
}
fn comparison_binary(
    format: MachineIntegerType,
    op: MachineBinaryOp,
    left: KernelTerm,
    right: KernelTerm,
) -> KernelTerm {
    let key = (format, op, left.id(), right.id());
    if crate::instrumentation::deadline_exceeded_with_work(1) {
        return KernelTerm::machine_binary_shared(format, op, [left, right]);
    }
    if let Some(result) = BINARY_RESULTS.with(|cache| cache.borrow().get(&key).cloned()) {
        return result;
    }
    let result = comparison_binary_uncached(format, op, left, right);
    if !crate::instrumentation::deadline_exceeded_with_work(0) {
        BINARY_RESULTS.with(|cache| cache.borrow_mut().insert(key, result.clone()));
    }
    result
}

fn comparison_binary_uncached(
    format: MachineIntegerType,
    op: MachineBinaryOp,
    left: KernelTerm,
    right: KernelTerm,
) -> KernelTerm {
    use MachineBinaryOp as O;
    use MachineIntegerType as T;
    let word32 = matches!(format, T::Int32 | T::UInt32);
    let restyle = |term: KernelTerm| {
        if word32 && let Some(value) = literal(&term) {
            imported(format, value.constant_in32(format))
        } else {
            term.with_machine_observation_type(format)
        }
    };
    let (left, right) = (restyle(left), restyle(right));
    let raw = |left, right| KernelTerm::machine_binary_shared(format, op, [left, right]);
    if op == O::Subtract && left == right {
        return constant(format, 0);
    }
    if !matches!(
        op,
        O::Add
            | O::Subtract
            | O::Multiply
            | O::Divide
            | O::Remainder
            | O::ShiftLeft
            | O::ShiftRight
    ) {
        return raw(left, right);
    }
    // Reuse the established evaluator only for two fixed-size literal leaves.
    // No symbolic child is exported or temporarily represented as a native tree.
    if let (Some(a), Some(b)) = (literal(&left), literal(&right)) {
        return imported(format, MachineTerm::machine_binary(format, op, a, b));
    }
    if word32 {
        match op {
            O::Add => {
                for (a, b) in [(&left, &right), (&right, &left)] {
                    if let Some([base, taken]) = binary(b, format, O::Subtract)
                        && taken == a
                    {
                        return base.clone();
                    }
                    if let (Some([zero, taken]), Some([first, second])) =
                        (binary(a, format, O::Subtract), binary(b, format, O::Add))
                        && word(zero) == Some(0)
                    {
                        if taken == first {
                            return second.clone();
                        }
                        if taken == second {
                            return first.clone();
                        }
                    }
                }
                if word(&right) == Some(0) {
                    return left;
                }
                if word(&left) == Some(0) {
                    return right;
                }
            }
            O::Subtract => {
                if word(&right) == Some(0) {
                    return left;
                }
                let (a, b) = (
                    binary(&left, format, O::Add),
                    binary(&right, format, O::Add),
                );
                if let (Some([a0, a1]), Some([b0, b1])) = (a, b) {
                    for (x, rest, y, other) in [
                        (a0, a1, b0, b1),
                        (a0, a1, b1, b0),
                        (a1, a0, b0, b1),
                        (a1, a0, b1, b0),
                    ] {
                        if x == y {
                            return comparison_binary(format, op, rest.clone(), other.clone());
                        }
                    }
                }
                if let Some([a, b]) = a {
                    if *a == right {
                        return b.clone();
                    }
                    if *b == right {
                        return a.clone();
                    }
                }
                if let Some([a, b]) = b {
                    if left == *a {
                        return comparison_binary(format, op, constant(format, 0), b.clone());
                    }
                    if left == *b {
                        return comparison_binary(format, op, constant(format, 0), a.clone());
                    }
                }
            }
            O::Multiply => {
                if word(&right) == Some(1) {
                    return left;
                }
                if word(&left) == Some(1) {
                    return right;
                }
                if word(&left) == Some(0) || word(&right) == Some(0) {
                    return constant(format, 0);
                }
            }
            O::Divide if word(&right) == Some(1) => return left,
            O::ShiftRight if word(&right) == Some(0) => return left,
            O::ShiftLeft if format == T::UInt32 && word(&right) == Some(0) => return left,
            _ => {}
        }
    } else if matches!(format, T::Int64 | T::UInt64) {
        let numeric = |term: &KernelTerm| {
            literal(term)
                .and_then(|value| format.constant_from_term(&value))
                .and_then(|value| value.to_i128())
        };
        if op == O::Multiply {
            if numeric(&right) == Some(1) {
                return left;
            }
            if numeric(&left) == Some(1) {
                return right;
            }
            if numeric(&left) == Some(0) || numeric(&right) == Some(0) {
                return constant(format, 0);
            }
        }
        if format == T::UInt64 {
            if matches!(op, O::Add | O::Subtract) && numeric(&right) == Some(0) {
                return left;
            }
            if op == O::Add && numeric(&left) == Some(0) {
                return right;
            }
            let inverse = match op {
                O::Add => Some(O::Subtract),
                O::Subtract => Some(O::Add),
                _ => None,
            };
            if let Some(inverse) = inverse
                && let Some([base, taken]) = binary(&left, format, inverse)
                && numeric(&right).is_some()
                && numeric(&right) == numeric(taken)
            {
                return base.clone();
            }
        }
    }
    raw(left, right)
}

#[cfg(test)]
fn comparison_read_fixture(value: MachineTerm) -> (Variable, Variable) {
    let ty = MachineIntegerType::Int32;
    let index = MachineTerm::Variable(Variable(992201));
    let pointer = |value| Pointer {
        block: PointerBlock::Concrete("opaque-comparison".into()),
        offset: PointerOffsetTerm::scaled_int32_node(value, 4),
    };
    let memory = crate::kernel::intern_memory(
        Memory::new()
            .with_block("opaque-comparison", 64)
            .store(pointer(index.clone()), ProgramValue::Int32(value)),
    );
    let written = MachineTerm::Binary {
        format: ty,
        op: MachineBinaryOp::Add,
        left: Box::new(index.clone()),
        right: Box::new(MachineTerm::constant(0)),
    };
    let load = crate::kernel::eval::load_variable_for_exact_cell(
        &memory,
        &pointer(written),
        crate::kernel::LoadKind::Int32,
        4,
    );
    let canonical = crate::kernel::eval::load_variable_for_exact_cell(
        &memory,
        &pointer(index),
        crate::kernel::LoadKind::Int32,
        4,
    );
    (load, canonical)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check_conditional_parity(
        format: MachineIntegerType,
        native: MachineTerm,
        guards: Vec<ConditionTerm>,
    ) {
        let root = imported(format, native.clone());
        for omitted in 0..=guards.len() {
            for refuted in [false, true] {
                let mut selected = PureFactContext::new();
                let mut conditions = HashMap::new();
                for (index, guard) in guards.iter().enumerate() {
                    if index == omitted && !refuted {
                        continue;
                    }
                    let truth = index != omitted;
                    conditions.insert(guard.clone(), truth);
                    selected = selected.assume_condition(guard.clone(), truth);
                }
                let expected = TermRewrite::for_conditions(&conditions).bits(&native);
                let exports = KernelTermExport::machine_export_count();
                let actual = TermRewrite::for_cited_conditions_with_context(
                    &conditions,
                    &selected,
                    &selected,
                )
                .shared_machine_operand(&root)
                .unwrap();
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                assert_eq!(
                    actual,
                    imported(format, expected.clone()),
                    "{native:?}, omitted={omitted}, refuted={refuted}; actual={:?}; expected={:?}",
                    actual.node(),
                    imported(format, expected.clone()).node()
                );
            }
        }
    }

    #[test]
    fn shared_conditional_remainders_preserve_selected_guards() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
            let n = MachineTerm::Binary {
                format,
                op: MachineBinaryOp::Add,
                left: MachineTerm::Variable(Variable(985001)).into(),
                right: MachineTerm::Variable(Variable(985002)).into(),
            };
            let constant = |number| {
                crate::kernel::machine_integer::range::constant_word(
                    format,
                    &num_bigint::BigInt::from(number),
                )
                .unwrap()
            };
            for divisor in [0, 1, 5] {
                let d = constant(divisor);
                let inputs = [
                    n.clone(),
                    MachineTerm::Binary {
                        format,
                        op: MachineBinaryOp::Subtract,
                        left: n.clone().into(),
                        right: d.clone().into(),
                    },
                    MachineTerm::Binary {
                        format,
                        op: MachineBinaryOp::Subtract,
                        left: n.clone().into(),
                        right: MachineTerm::Binary {
                            format,
                            op: MachineBinaryOp::Remainder,
                            left: n.clone().into(),
                            right: d.clone().into(),
                        }
                        .into(),
                    },
                ];
                for input in inputs {
                    let native = MachineTerm::Binary {
                        format,
                        op: MachineBinaryOp::Remainder,
                        left: input.into(),
                        right: d.clone().into(),
                    };
                    let guards = native
                        .guarded_remainder_rewrite()
                        .map(|(guards, _)| guards)
                        .unwrap_or_default();
                    check_conditional_parity(format, native, guards);
                }
            }
        }
    }

    #[test]
    fn shared_conditional_low_word_multiple_requires_the_full_width_bound() {
        let _session = crate::kernel::VerificationSession::enter();
        use MachineIntegerType as T;
        let n = MachineTerm::uint64_add(
            MachineTerm::Variable(Variable(985021)),
            MachineTerm::Variable(Variable(985022)),
        );
        let d = MachineTerm::uint64_constant(5);
        let multiple = MachineTerm::uint64_subtract(n.clone(), MachineTerm::uint64_remainder(n, d));
        let low = MachineTerm::uint32_from_64(multiple);
        for low in [
            low.clone(),
            MachineTerm::sign_cast32(T::UInt32, T::Int32, low),
        ] {
            let input = MachineTerm::Binary {
                format: T::Int32,
                op: MachineBinaryOp::Remainder,
                left: low.into(),
                right: MachineTerm::constant(5).into(),
            };
            let guards = input.guarded_remainder_rewrite().unwrap().0;
            check_conditional_parity(T::Int32, input, guards);
        }
    }

    #[test]
    fn shared_conditional_narrowing_preserves_source_width_and_every_bound() {
        let _session = crate::kernel::VerificationSession::enter();
        use MachineIntegerType as T;
        for source in [
            T::Int8,
            T::UInt8,
            T::Int16,
            T::UInt16,
            T::Int32,
            T::UInt32,
            T::Int64,
            T::UInt64,
        ] {
            for destination in [T::Int8, T::UInt8, T::Int16, T::UInt16] {
                let value = if source.format().bits() >= 32 {
                    MachineTerm::Binary {
                        format: source,
                        op: MachineBinaryOp::Add,
                        left: MachineTerm::Variable(Variable(985011)).into(),
                        right: MachineTerm::Variable(Variable(985012)).into(),
                    }
                } else {
                    MachineTerm::Variable(Variable(985011))
                };
                let Some((bounds, _)) =
                    crate::kernel::assumptions::narrowed_cast_identity(&value, source, destination)
                else {
                    continue;
                };
                let native = MachineTerm::Cast {
                    spelling: MachineCastSpelling::Generic,
                    from: destination,
                    to: T::Int32,
                    value: MachineTerm::Cast {
                        spelling: MachineCastSpelling::Generic,
                        from: source,
                        to: destination,
                        value: value.into(),
                    }
                    .into(),
                };
                let guards = bounds
                    .into_iter()
                    .map(|bound| bound.conditions[0].clone())
                    .collect();
                check_conditional_parity(T::Int32, native, guards);
            }
        }
    }

    #[test]
    fn unguarded_machine_observation_copy_keeps_shared_operands() {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let native = MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            from: format,
            to: format,
            value: Box::new(MachineTerm::add(
                MachineTerm::Variable(Variable(992400)),
                1u32.into(),
            )),
        };
        let expected = TermRewrite::empty().bits(&native);
        let input = IntegerTerm::Machine(
            SharedMachineIntegerTerm::from_shared(format, imported(format, native)).unwrap(),
        );
        let expected = IntegerTerm::from_machine(format, expected).unwrap();
        let exports = KernelTermExport::machine_export_count();
        assert_eq!(TermRewrite::empty().integer(&input), expected);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn exact_integer_rewrites_preserve_shared_operator_and_cast_syntax() {
        let _session = crate::kernel::VerificationSession::enter();
        let source: SharedIntegerTerm = IntegerTerm::Variable(Variable(992401)).into();
        let target: SharedIntegerTerm = IntegerTerm::constant_i64(7).into();
        let formats = [
            MachineIntegerType::Int8,
            MachineIntegerType::UInt8,
            MachineIntegerType::Int16,
            MachineIntegerType::UInt16,
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ];
        for format in formats {
            let conversion = MachineTerm::IntegerToMachine {
                value: source.clone(),
                destination: format,
            };
            let expression = MachineTerm::Binary {
                format,
                op: MachineBinaryOp::Add,
                left: Box::new(conversion.clone()),
                right: Box::new(conversion),
            };
            for destination in formats {
                for native in [
                    MachineTerm::Cast {
                        spelling: MachineCastSpelling::Generic,
                        from: format,
                        to: destination,
                        value: Box::new(expression.clone()),
                    },
                    MachineTerm::machine_integer_cast(format, destination, expression.clone()),
                ] {
                    let expected = TermRewrite::for_integer_exact(&source, &target).bits(&native);
                    let input = IntegerTerm::Machine(
                        SharedMachineIntegerTerm::from_shared(
                            destination,
                            imported(destination, native),
                        )
                        .unwrap(),
                    );
                    let expected = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                        destination,
                        expected,
                    ));
                    let exports = KernelTermExport::machine_export_count();
                    let mut rewrite = TermRewrite::for_integer_exact(&source, &target);
                    assert_eq!(
                        rewrite.integer(&input),
                        expected,
                        "{format:?} to {destination:?}"
                    );
                    assert!(rewrite.changed);
                    assert!(rewrite.refusal().is_none());
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                }
            }
        }
    }

    #[test]
    fn compound_machine_replacement_is_exact_and_does_not_rewrite_its_replacement() {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let a = MachineTerm::Variable(Variable(992402));
        let b = MachineTerm::Variable(Variable(992403));
        let source = MachineTerm::add(a.clone(), b.clone());
        let replacement = MachineTerm::add(source.clone(), a.clone());
        for native in [
            source.clone(),
            MachineTerm::Binary {
                format,
                op: MachineBinaryOp::Multiply,
                left: Box::new(source.clone()),
                right: Box::new(source.clone()),
            },
            MachineTerm::add(b, a),
        ] {
            let expected = TermRewrite::for_bits_checked(&source, &replacement).bits(&native);
            let root = imported(format, native);
            let exports = KernelTermExport::machine_export_count();
            let actual = TermRewrite::for_bits_checked(&source, &replacement)
                .shared_machine_operand(&root)
                .unwrap();
            assert_eq!(actual, imported(format, expected));
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }

    #[test]
    fn exact_machine_literal_sources_keep_the_native_carrier_match() {
        let _session = crate::kernel::VerificationSession::enter();
        for (format, values) in [
            (
                MachineIntegerType::Int32,
                vec![MachineTerm::constant(1), MachineTerm::uint32_constant(1)],
            ),
            (
                MachineIntegerType::UInt32,
                vec![
                    MachineTerm::constant(u32::MAX),
                    MachineTerm::uint32_constant(u32::MAX),
                ],
            ),
            (
                MachineIntegerType::Int64,
                vec![
                    MachineTerm::int64_constant(-1),
                    MachineTerm::uint64_constant(u64::MAX),
                ],
            ),
            (
                MachineIntegerType::UInt64,
                vec![
                    MachineTerm::int64_constant(1),
                    MachineTerm::uint64_constant(1),
                ],
            ),
        ] {
            let replacement =
                crate::kernel::machine_integer::range::constant_word(format, &7.into()).unwrap();
            for source in &values {
                for native in &values {
                    let expected = TermRewrite::for_bits_checked(source, &replacement).bits(native);
                    let root = imported(format, native.clone());
                    let exports = KernelTermExport::machine_export_count();
                    let actual = TermRewrite::for_bits_checked(source, &replacement)
                        .shared_machine_operand(&root)
                        .unwrap();
                    assert_eq!(
                        actual,
                        imported(format, expected),
                        "{format:?}: {source:?} in {native:?}"
                    );
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                }
            }
        }
    }

    #[test]
    fn shared_integer_and_typed_variable_substitutions_preserve_scope() {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let variable = Variable(992404);
        let replacement = IntegerTerm::constant_i64(5);
        let source = MachineTerm::IntegerToMachine {
            value: IntegerTerm::Variable(variable).into(),
            destination: format,
        };
        let native = MachineTerm::Binary {
            format,
            op: MachineBinaryOp::Multiply,
            left: Box::new(source),
            right: Box::new(MachineTerm::Variable(variable)),
        };
        let root = imported(format, native.clone());
        let empty = BTreeMap::new();
        for shadowed in [false, true] {
            let expected =
                TermRewrite::for_integer_variables(variable, &replacement, shadowed, &empty)
                    .bits(&native);
            let exports = KernelTermExport::machine_export_count();
            let actual =
                TermRewrite::for_integer_variables(variable, &replacement, shadowed, &empty)
                    .shared_machine_operand(&root)
                    .unwrap();
            assert_eq!(actual, imported(format, expected));
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
        let c = BTreeMap::from([(
            variable,
            TypedProgramValueReplacement::Bitvector(9u32.into()),
        )]);
        let integer = BTreeMap::from([(variable, replacement)]);
        let algebraic = BTreeMap::new();
        let expected = TermRewrite::for_typed_variables(&c, &integer, &algebraic).bits(&native);
        let exports = KernelTermExport::machine_export_count();
        let actual = TermRewrite::for_typed_variables(&c, &integer, &algebraic)
            .shared_machine_operand(&root)
            .unwrap();
        assert_eq!(actual, imported(format, expected));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn variable_substitution_preserves_shared_arithmetic_and_is_query_local() {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = MachineTerm::Variable(Variable(992301));
        let formats = [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ];
        for format in formats {
            for op in [
                MachineBinaryOp::Add,
                MachineBinaryOp::Subtract,
                MachineBinaryOp::Multiply,
                MachineBinaryOp::Divide,
                MachineBinaryOp::Remainder,
                MachineBinaryOp::ShiftLeft,
                MachineBinaryOp::ShiftRight,
                MachineBinaryOp::BitwiseAnd,
            ] {
                let native = MachineTerm::Binary {
                    format,
                    op,
                    left: Box::new(variable.clone()),
                    right: Box::new(variable.clone()),
                };
                let root = imported(format, native.clone());
                for number in [0, 1, 7] {
                    let replacement = crate::kernel::machine_integer::range::constant_word(
                        format,
                        &number.into(),
                    )
                    .unwrap();
                    let expected =
                        TermRewrite::for_bits_checked(&variable, &replacement).bits(&native);
                    let exports = KernelTermExport::machine_export_count();
                    let mut rewrite = TermRewrite::for_bits_checked(&variable, &replacement);
                    // Registered-read mode must not share replacement-dependent results.
                    rewrite.enable_registered_load_resolution();
                    let result = rewrite.shared_machine_operand(&root).unwrap();
                    assert_eq!(result, imported(format, expected));
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                }
            }
        }
    }

    #[test]
    fn signed_observation_retains_a_substituted_unsigned_carrier() {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int64;
        let source = MachineTerm::Variable(Variable(992303));
        let replacement = MachineTerm::uint64_constant(u64::MAX);
        let input = IntegerTerm::Machine(
            SharedMachineIntegerTerm::from_shared(format, imported(format, source.clone()))
                .unwrap(),
        );
        let expected =
            IntegerTerm::from_machine(format, replacement.clone()).unwrap_or_else(|| {
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    format,
                    replacement.clone(),
                ))
            });
        let exports = KernelTermExport::machine_export_count();
        let actual = TermRewrite::for_bits_checked(&source, &replacement).integer(&input);
        assert_eq!(actual, expected);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn variable_substitution_preserves_shared_cast_rules() {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = MachineTerm::Variable(Variable(992302));
        let formats = [
            MachineIntegerType::Int8,
            MachineIntegerType::UInt8,
            MachineIntegerType::Int16,
            MachineIntegerType::UInt16,
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ];
        for source in formats {
            for destination in formats {
                let native = MachineTerm::Cast {
                    spelling: MachineCastSpelling::Generic,
                    from: source,
                    to: destination,
                    value: Box::new(variable.clone()),
                };
                let root = imported(destination, native.clone());
                for replacement in [
                    variable.clone(),
                    crate::kernel::machine_integer::range::constant_word(source, &1.into())
                        .unwrap(),
                ] {
                    let expected =
                        TermRewrite::for_bits_checked(&variable, &replacement).bits(&native);
                    let exports = KernelTermExport::machine_export_count();
                    let result = TermRewrite::for_bits_checked(&variable, &replacement)
                        .shared_machine_operand(&root)
                        .unwrap();
                    assert_eq!(
                        result,
                        imported(destination, expected),
                        "{source:?} to {destination:?}"
                    );
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                }
            }
        }
    }

    #[test]
    fn comparison_keeps_arithmetic_shared_when_a_read_exposes_an_integer_conversion() {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let opaque = MachineTerm::IntegerToMachine {
            value: IntegerTerm::Variable(Variable(992202)).into(),
            destination: ty,
        };
        let (load, _) = comparison_read_fixture(opaque.clone());
        let rewritten = TermRewrite::for_arithmetic_comparison().bits(&MachineTerm::Variable(load));
        assert_eq!(rewritten, opaque);

        let mut root = imported(ty, MachineTerm::Variable(load));
        for _ in 0..4 {
            root = KernelTerm::machine_binary_shared(
                ty,
                MachineBinaryOp::Add,
                [root.clone(), root.clone()],
            );
        }
        let proposition = Proposition::ConditionIs(
            ConditionTerm::integer_less_than(
                IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(ty, root).unwrap()),
                IntegerTerm::constant_i64(0),
            ),
            true,
        );
        let exports = KernelTermExport::machine_export_count();
        let _ = TermRewrite::arithmetic_comparison(&proposition);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn comparison_rewrite_preserves_values_and_state_separation() {
        let _session = crate::kernel::VerificationSession::enter();
        let facts = PureFactContext::new();
        let (seven, canonical_seven) = comparison_read_fixture(7u32.into());
        let (eight, _) = comparison_read_fixture(8u32.into());
        let (unknown, _) = comparison_read_fixture(MachineTerm::IntegerToMachine {
            value: IntegerTerm::Variable(Variable(992202)).into(),
            destination: MachineIntegerType::Int32,
        });
        let var = MachineTerm::Variable;
        for (left, right, expected) in [
            (var(seven), var(canonical_seven), Some(true)),
            (var(seven), 7u32.into(), Some(true)),
            (var(eight), 7u32.into(), Some(false)),
            (var(seven), var(eight), Some(false)),
            (var(unknown), 7u32.into(), None),
        ] {
            assert_eq!(
                {
                    let written = Proposition::ConditionIs(
                        ConditionTerm::equal(left.clone(), right.clone()),
                        true,
                    );
                    let normalized =
                        TermRewrite::arithmetic_comparison(&written).unwrap_or(written);
                    let Proposition::ConditionIs(condition, true) = normalized else {
                        unreachable!()
                    };
                    facts.decide(&condition)
                },
                expected,
                "{left:?} == {right:?}"
            );
        }
    }

    #[test]
    fn comparison_preserves_stored_value_premise_matching() {
        let _session = crate::kernel::VerificationSession::enter();
        let (read, _) = comparison_read_fixture(7u32.into());
        let bound = MachineTerm::Variable(Variable(992203));
        let claim = |value| {
            Proposition::ConditionIs(ConditionTerm::signed_less_than(value, bound.clone()), true)
        };
        assert!(
            crate::kernel::proof::fact_reasoning::condition_polarity_equivalent(
                &claim(MachineTerm::Variable(read)),
                &claim(7u32.into())
            )
        );
    }

    #[test]
    fn shared_integer_conversions_preserve_carriers_and_equality_authority() {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let a = Variable(992211);
        let b = Variable(992212);
        let c = Variable(992213);
        let expression = |integer| {
            imported(
                format,
                MachineTerm::Binary {
                    format,
                    op: MachineBinaryOp::Add,
                    left: Box::new(MachineTerm::IntegerToMachine {
                        destination: format,
                        value: IntegerTerm::Add(
                            IntegerTerm::Variable(integer).into(),
                            IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                                format,
                                MachineTerm::Variable(a),
                            ))
                            .into(),
                        )
                        .into(),
                    }),
                    right: Box::new(MachineTerm::Variable(c)),
                },
            )
        };
        let (left, right) = (expression(a), expression(b));
        let exports = KernelTermExport::machine_export_count();
        let observed = |root| SharedMachineIntegerTerm::from_shared(format, root).unwrap();
        let mut carriers = CarrierVariables::default();
        collect_machine_carriers(&observed(left.clone()), &mut carriers);
        assert_eq!(carriers.program_values, BTreeSet::from([a, c]));
        assert_eq!(carriers.integer, BTreeSet::from([a]));
        assert!(carriers.algebraic.is_empty());
        let condition = ConditionTerm::integer_equal(
            IntegerTerm::Machine(observed(left.clone())),
            IntegerTerm::Machine(observed(right)),
        );
        let parent = PureFactContext::new();
        assert_eq!(parent.decide(&condition), None);
        let child = parent.clone().assume_condition(
            ConditionTerm::integer_equal(IntegerTerm::Variable(a), IntegerTerm::Variable(b)),
            true,
        );
        assert_eq!(child.decide(&condition), Some(true));
        assert_eq!(parent.decide(&condition), None);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        // Explicit output still reconstructs the exact source and imports to
        // the same identity after the original boxed source has been dropped.
        let native = KernelTermExport::machine(&left).unwrap();
        assert_eq!(imported(format, native), left);
    }

    #[test]
    fn shared_comparison_reconstruction_matches_native_casts() {
        let _session = crate::kernel::VerificationSession::enter();
        let formats = [
            MachineIntegerType::Int8,
            MachineIntegerType::UInt8,
            MachineIntegerType::Int16,
            MachineIntegerType::UInt16,
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ];
        for source in formats {
            for destination in formats {
                for inner in [
                    MachineTerm::Variable(Variable(992100)),
                    crate::kernel::machine_integer::range::constant_word(source, &1.into())
                        .unwrap(),
                ] {
                    for native in [
                        MachineTerm::Cast {
                            spelling: MachineCastSpelling::Generic,
                            from: source,
                            to: destination,
                            value: Box::new(inner.clone()),
                        },
                        MachineTerm::machine_integer_cast(source, destination, inner.clone()),
                        MachineTerm::Cast {
                            spelling: MachineCastSpelling::Generic,
                            from: source,
                            to: destination,
                            value: Box::new(MachineTerm::Cast {
                                spelling: MachineCastSpelling::Generic,
                                from: destination,
                                to: source,
                                value: Box::new(MachineTerm::Variable(Variable(992101))),
                            }),
                        },
                    ] {
                        let expected = TermRewrite::for_arithmetic_comparison().bits(&native);
                        let root = imported(destination, native.clone());
                        let exports = KernelTermExport::machine_export_count();
                        let actual = TermRewrite::for_arithmetic_comparison()
                            .shared_machine_operand(&root)
                            .unwrap();
                        assert_eq!(KernelTermExport::machine_export_count(), exports);
                        assert_eq!(actual, imported(destination, expected), "{native:?}");
                    }
                }
            }
        }
    }

    #[test]
    fn shared_comparison_reconstruction_matches_native_arithmetic() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let x = MachineTerm::Variable(Variable(992001));
            let y = MachineTerm::Variable(Variable(992002));
            let zero =
                crate::kernel::machine_integer::range::constant_word(format, &0.into()).unwrap();
            let one =
                crate::kernel::machine_integer::range::constant_word(format, &1.into()).unwrap();
            let make = |op, a: MachineTerm, b: MachineTerm| MachineTerm::Binary {
                format,
                op,
                left: Box::new(a),
                right: Box::new(b),
            };
            let add = make(MachineBinaryOp::Add, x.clone(), y.clone());
            let sub = make(MachineBinaryOp::Subtract, x.clone(), y.clone());
            let neg = make(MachineBinaryOp::Subtract, zero.clone(), x.clone());
            let cases = [x.clone(), y, zero, one, add, sub, neg];
            for op in [
                MachineBinaryOp::Add,
                MachineBinaryOp::Subtract,
                MachineBinaryOp::Multiply,
                MachineBinaryOp::Divide,
                MachineBinaryOp::Remainder,
                MachineBinaryOp::ShiftLeft,
                MachineBinaryOp::ShiftRight,
                MachineBinaryOp::BitwiseAnd,
            ] {
                for left in &cases {
                    for right in &cases {
                        let native = make(op, left.clone(), right.clone());
                        let expected = TermRewrite::for_arithmetic_comparison().bits(&native);
                        let root = imported(format, native);
                        let exports = KernelTermExport::machine_export_count();
                        let result = TermRewrite::for_arithmetic_comparison()
                            .shared_machine_operand(&root)
                            .unwrap();
                        assert_eq!(KernelTermExport::machine_export_count(), exports);
                        assert_eq!(
                            result,
                            imported(format, expected),
                            "{format:?} {op:?}: {left:?} {right:?}"
                        );
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    use super::*;
    include!("../../../scaling_tests/kernel/proof/shared_comparison.rs");
}

#[cfg(test)]
mod call_tests {
    use super::*;

    fn call(format: MachineIntegerType, argument: KernelTerm) -> KernelTerm {
        let application = SharedPureApplication::intern(
            "rewrite_call".into(),
            vec![PureFunctionArgument::SharedMachine(
                SharedMachineIntegerTerm::from_shared(MachineIntegerType::Int32, argument).unwrap(),
            )],
        );
        KernelTermImport::default().machine_call(format, &application)
    }

    #[test]
    fn common_calls_rewrite_arguments_and_keep_exact_noop_roots() {
        let _session = VerificationSession::enter();
        let from = MachineTerm::Variable(Variable(995860));
        let to = MachineTerm::Variable(Variable(995861));
        let missing = MachineTerm::Variable(Variable(995862));
        for format in crate::kernel::machine_integer::FORMATS {
            let argument =
                KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(995860));
            let root = call(format, argument);
            let native = KernelTermExport::machine(&root).unwrap();
            let expected = TermRewrite::for_bits_checked(&from, &to).bits(&native);
            let exports = KernelTermExport::machine_export_count();
            let mut rewrite = TermRewrite::for_bits_checked(&from, &to);
            let result = rewrite.shared_machine_operand(&root).unwrap();
            assert_eq!(rewrite.refusal(), None);
            assert!(matches!(result.node(), KernelTermNode::Call { .. }));
            assert_ne!(result, root);
            let mut noop = TermRewrite::for_bits_checked(&missing, &to);
            assert_eq!(noop.shared_machine_operand(&root), Some(root.clone()));
            assert_eq!(noop.refusal(), None);
            let mut exact = TermRewrite::for_machine_operands_checked(
                MachineOperandView::Shared(&root),
                MachineOperandView::Legacy(&to),
            );
            assert_eq!(exact.bits(&native), to);
            assert_eq!(exact.refusal(), None);
            let mut matcher = crate::kernel::proof::machine_source_match::MachineSourceMatcher::new(
                MachineOperandView::Legacy(&native),
            );
            assert_eq!(matcher.matches(format, &root), Some(true));
            assert_eq!(matcher.matches(format, &result), Some(false));
            let legacy = KernelTerm::retained_native_machine_operand(format, &native);
            assert!(crate::kernel::shared_machine_syntax_equal(&root, &legacy));
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert_eq!(KernelTermExport::machine(&result).unwrap(), expected);
        }
    }

    #[test]
    fn common_call_substitution_preserves_capture_avoidance_inside_arguments() {
        let _session = VerificationSession::enter();
        let from = MachineTerm::Variable(Variable(995890));
        let to = MachineTerm::Variable(Variable(995891));
        let fold = MachineTerm::RangeFold {
            start: Box::new(MachineTerm::constant(0)),
            end: Box::new(MachineTerm::constant(3)),
            initial: Box::new(from.clone()),
            accumulator: Variable(995891),
            item: Variable(995892),
            body: Box::new(MachineTerm::add(to.clone(), from.clone())),
        };
        let application = SharedPureApplication::intern(
            "binder_call".into(),
            vec![PureFunctionArgument::Value(ProgramValue::Int32(fold))],
        );
        let root =
            KernelTermImport::default().machine_call(MachineIntegerType::Int32, &application);
        let native = KernelTermExport::machine(&root).unwrap();
        let mut native_rewrite = TermRewrite::for_bits_checked(&from, &to);
        let expected = native_rewrite.bits(&native);
        assert_eq!(native_rewrite.refusal(), None);
        let exports = KernelTermExport::machine_export_count();
        let mut rewrite = TermRewrite::for_bits_checked(&from, &to);
        let result = rewrite.shared_machine_operand(&root).unwrap();
        assert_eq!(rewrite.refusal(), None);
        assert!(matches!(result.node(), KernelTermNode::Call { .. }));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        let actual = KernelTermExport::machine(&result).unwrap();
        assert_eq!(actual, expected);
        let MachineTerm::ClickFunctionApplication { arguments, .. } = actual else {
            panic!()
        };
        let PureFunctionArgument::Value(ProgramValue::Int32(MachineTerm::RangeFold {
            accumulator,
            ..
        })) = &arguments[0]
        else {
            panic!()
        };
        assert_ne!(*accumulator, Variable(995891));
    }

    mod scaling_tests {
        use super::*;
        include!("../../../scaling_tests/kernel/proof/shared_call_rewrites.rs");
    }
}
