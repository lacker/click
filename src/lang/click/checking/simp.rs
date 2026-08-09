use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::lang::click) enum SimpProposition {
    True,
    False,
    Proposition(Proposition),
}

pub(in crate::lang::click) fn normalize_proposition(proposition: &Proposition) -> SimpProposition {
    match proposition {
        Proposition::Equal(left, right) => match simp_terms_equal(left, right) {
            Some(true) => SimpProposition::True,
            Some(false) => SimpProposition::False,
            None => {
                SimpProposition::Proposition(Proposition::Equal(simp_term(left), simp_term(right)))
            }
        },
        Proposition::ConditionIs(condition, expected) => {
            match simp_condition_without_assumptions(condition) {
                Some(actual) if actual == *expected => SimpProposition::True,
                Some(_) => SimpProposition::False,
                None => SimpProposition::Proposition(proposition.clone()),
            }
        }
        Proposition::And(left, right) => {
            let left = normalize_proposition(left);
            let right = normalize_proposition(right);
            match (left, right) {
                (SimpProposition::False, _) | (_, SimpProposition::False) => SimpProposition::False,
                (SimpProposition::True, SimpProposition::True) => SimpProposition::True,
                (SimpProposition::True, right) => right,
                (left, SimpProposition::True) => left,
                (left, right) => SimpProposition::Proposition(Proposition::And(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        Proposition::Or(left, right) => {
            let left = normalize_proposition(left);
            let right = normalize_proposition(right);
            match (left, right) {
                (SimpProposition::True, _) | (_, SimpProposition::True) => SimpProposition::True,
                (SimpProposition::False, SimpProposition::False) => SimpProposition::False,
                (SimpProposition::False, right) => right,
                (left, SimpProposition::False) => left,
                (left, right) => SimpProposition::Proposition(Proposition::Or(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        Proposition::Not(body) => match normalize_proposition(body) {
            SimpProposition::True => SimpProposition::False,
            SimpProposition::False => SimpProposition::True,
            body => {
                SimpProposition::Proposition(Proposition::Not(Box::new(body.into_proposition())))
            }
        },
        Proposition::Implies(left, right) => {
            let left = normalize_proposition(left);
            let right = normalize_proposition(right);
            match (left, right) {
                (SimpProposition::False, _) | (_, SimpProposition::True) => SimpProposition::True,
                (SimpProposition::True, right) => right,
                (_, SimpProposition::False) => SimpProposition::False,
                (left, right) => SimpProposition::Proposition(Proposition::Implies(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        _ => SimpProposition::Proposition(proposition.clone()),
    }
}

pub(in crate::lang::click) fn rewrite_proposition_by_exact_equality(
    goal: &Proposition,
    equality: &Proposition,
    available: &[Proposition],
) -> Result<Proposition, String> {
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) = equality
    else {
        return Err("`rewrite` currently expects an int32 equality".to_string());
    };
    let reverse = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(right.as_ref().clone()),
            Box::new(left.as_ref().clone()),
        ),
        true,
    );
    if !available.contains(equality) && !available.contains(&reverse) {
        return Err(format!(
            "`rewrite` requires an exact available equality, missing {equality:?}"
        ));
    }
    let Bitvector32Term::Variable(variable) = left.as_ref() else {
        return Err(
            "`rewrite` currently requires the equality's left side to be an int32 variable"
                .to_string(),
        );
    };
    let rewritten =
        substitute_int32_variable_in_proposition(goal, *variable, right.as_ref().clone());
    if &rewritten == goal {
        return Err("`rewrite` equality does not occur in the current goal".to_string());
    }
    Ok(rewritten)
}

/// Plan a surface proof made only of explicit equality substitutions followed
/// by an exact assumption or context-free normalization.
pub(in crate::lang::click) fn plan_explicit_equality_rewrites(
    goal: &Proposition,
    premises: &[(Proposition, ClickProposition)],
    available: &[Proposition],
) -> Option<Vec<ProofTactic>> {
    fn search(
        current: Proposition,
        premises: &[(Proposition, ClickProposition)],
        available: &[Proposition],
        used: &mut [bool],
        tactics: &mut Vec<ProofTactic>,
    ) -> bool {
        if available.contains(&current) {
            tactics.push(ProofTactic::Assumption);
            return true;
        }
        if matches!(normalize_proposition(&current), SimpProposition::True) {
            tactics.push(ProofTactic::Normalize);
            return true;
        }
        for (index, (kernel, surface)) in premises.iter().enumerate() {
            if used[index] {
                continue;
            }
            let Ok(rewritten) = rewrite_proposition_by_exact_equality(&current, kernel, available)
            else {
                continue;
            };
            used[index] = true;
            tactics.push(ProofTactic::Rewrite(surface.clone()));
            if search(rewritten, premises, available, used, tactics) {
                return true;
            }
            tactics.pop();
            used[index] = false;
        }
        false
    }

    let mut used = vec![false; premises.len()];
    let mut tactics = Vec::new();
    search(goal.clone(), premises, available, &mut used, &mut tactics).then_some(tactics)
}

pub(in crate::lang::click) fn normalize_direct_atomic_memory_loads(
    proposition: &Proposition,
) -> Proposition {
    let normalize_pointer = |pointer: &Pointer| Pointer {
        block: pointer.block.clone(),
        offset: normalize_direct_atomic_pointer_offset_loads(&pointer.offset),
    };
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            let binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
                (
                    normalize_direct_atomic_memory_load(left),
                    normalize_direct_atomic_memory_load(right),
                )
            };
            let condition = match condition {
                ConditionTerm::Bitvector32SignedLessThan(left, right) => {
                    let (left, right) = binary(left, right);
                    ConditionTerm::Bitvector32SignedLessThan(Box::new(left), Box::new(right))
                }
                ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
                    let (left, right) = binary(left, right);
                    ConditionTerm::Bitvector32SignedLessEqual(Box::new(left), Box::new(right))
                }
                ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
                    let (left, right) = binary(left, right);
                    ConditionTerm::Bitvector32SignedGreaterThan(Box::new(left), Box::new(right))
                }
                ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
                    let (left, right) = binary(left, right);
                    ConditionTerm::Bitvector32SignedGreaterEqual(Box::new(left), Box::new(right))
                }
                ConditionTerm::Bitvector32Equal(left, right) => {
                    let (left, right) = binary(left, right);
                    ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right))
                }
                ConditionTerm::PointerOffsetEqual(left, right) => {
                    ConditionTerm::PointerOffsetEqual(
                        Box::new(normalize_direct_atomic_pointer_offset_loads(left)),
                        Box::new(normalize_direct_atomic_pointer_offset_loads(right)),
                    )
                }
                _ => return proposition.clone(),
            };
            Proposition::ConditionIs(condition, *value)
        }
        Proposition::CMemoryCanStore {
            memory,
            pointer,
            byte_width,
        } => Proposition::CMemoryCanStore {
            memory: memory.clone(),
            pointer: normalize_pointer(pointer),
            byte_width: *byte_width,
        },
        Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
        } => Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: normalize_pointer(base),
            bytes: normalize_direct_atomic_memory_load(bytes),
        },
        Proposition::CMemoryDisjoint {
            left_base,
            left_start,
            left_end,
            right_base,
            right_start,
            right_end,
        } => Proposition::CMemoryDisjoint {
            left_base: normalize_pointer(left_base),
            left_start: normalize_direct_atomic_memory_load(left_start),
            left_end: normalize_direct_atomic_memory_load(left_end),
            right_base: normalize_pointer(right_base),
            right_start: normalize_direct_atomic_memory_load(right_start),
            right_end: normalize_direct_atomic_memory_load(right_end),
        },
        Proposition::CResourceSeparate { left, right } => Proposition::CResourceSeparate {
            left: normalize_direct_atomic_resource_loads(left),
            right: normalize_direct_atomic_resource_loads(right),
        },
        Proposition::CResourceContains { parent, child } => Proposition::CResourceContains {
            parent: normalize_direct_atomic_resource_loads(parent),
            child: normalize_direct_atomic_resource_loads(child),
        },
        _ => proposition.clone(),
    }
}

fn normalize_direct_atomic_resource_loads(resource: &CResource) -> CResource {
    let normalize_value = |value: &CValue| match value {
        CValue::Void => CValue::Void,
        CValue::Int32(value) => CValue::Int32(normalize_direct_atomic_memory_load(value)),
        CValue::UInt8(value) => CValue::UInt8(normalize_direct_atomic_memory_load(value)),
        CValue::Pointer(pointer) => CValue::Pointer(Pointer {
            block: pointer.block.clone(),
            offset: normalize_direct_atomic_pointer_offset_loads(&pointer.offset),
        }),
    };
    match resource {
        CResource::Memory(range) => CResource::Memory(CMemoryRange::new(
            Pointer {
                block: range.base().block.clone(),
                offset: normalize_direct_atomic_pointer_offset_loads(&range.base().offset),
            },
            normalize_direct_atomic_memory_load(range.start()),
            normalize_direct_atomic_memory_load(range.end()),
        )),
        CResource::Composite { name, arguments } => CResource::Composite {
            name: name.clone(),
            arguments: arguments.iter().map(normalize_value).collect(),
        },
        CResource::Token { name, arguments } => CResource::Token {
            name: name.clone(),
            arguments: arguments.iter().map(normalize_value).collect(),
        },
    }
}

pub(super) fn normalize_direct_atomic_pointer_offset_loads(
    term: &PointerOffsetTerm,
) -> PointerOffsetTerm {
    match term {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => term.clone(),
        PointerOffsetTerm::Add(left, right) => PointerOffsetTerm::Add(
            Box::new(normalize_direct_atomic_pointer_offset_loads(left)),
            Box::new(normalize_direct_atomic_pointer_offset_loads(right)),
        ),
        PointerOffsetTerm::Int32Scaled { value, byte_width } => PointerOffsetTerm::Int32Scaled {
            value: Box::new(normalize_direct_atomic_memory_load(value)),
            byte_width: *byte_width,
        },
    }
}

fn normalize_direct_atomic_memory_load(term: &Bitvector32Term) -> Bitvector32Term {
    thread_local! {
        static CACHE: std::cell::RefCell<
            std::collections::HashMap<Bitvector32Term, Bitvector32Term>,
        > = std::cell::RefCell::new(std::collections::HashMap::new());
    }
    const CACHE_LIMIT: usize = 200_000;

    if let Some(normalized) = CACHE.with(|cache| cache.borrow().get(term).cloned()) {
        return normalized;
    }
    let normalized = normalize_direct_atomic_memory_load_uncached(term);
    CACHE.with(|cache| {
        let mut cache = cache.borrow_mut();
        if cache.len() >= CACHE_LIMIT {
            cache.clear();
        }
        cache.insert(term.clone(), normalized.clone());
    });
    normalized
}

fn normalize_direct_atomic_memory_load_uncached(term: &Bitvector32Term) -> Bitvector32Term {
    let binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
        (
            Box::new(normalize_direct_atomic_memory_load(left)),
            Box::new(normalize_direct_atomic_memory_load(right)),
        )
    };
    match term {
        Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => term.clone(),
        Bitvector32Term::Add(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::Add(left, right)
        }
        Bitvector32Term::Subtract(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::Subtract(left, right)
        }
        Bitvector32Term::Multiply(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::Multiply(left, right)
        }
        Bitvector32Term::Divide(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::Divide(left, right)
        }
        Bitvector32Term::Remainder(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::Remainder(left, right)
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::ShiftLeft(left, right)
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::ArithmeticShiftRight(left, right)
        }
        Bitvector32Term::BitwiseAnd(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::BitwiseAnd(left, right)
        }
        Bitvector32Term::BitwiseOr(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::BitwiseOr(left, right)
        }
        Bitvector32Term::BitwiseXor(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::BitwiseXor(left, right)
        }
        Bitvector32Term::BitwiseNot(value) => {
            Bitvector32Term::BitwiseNot(Box::new(normalize_direct_atomic_memory_load(value)))
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => Bitvector32Term::If {
            condition: condition.clone(),
            then_term: Box::new(normalize_direct_atomic_memory_load(then_term)),
            else_term: Box::new(normalize_direct_atomic_memory_load(else_term)),
        },
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => Bitvector32Term::RangeFold {
            start: Box::new(normalize_direct_atomic_memory_load(start)),
            end: Box::new(normalize_direct_atomic_memory_load(end)),
            initial: Box::new(normalize_direct_atomic_memory_load(initial)),
            accumulator: *accumulator,
            item: *item,
            body: Box::new(normalize_direct_atomic_memory_load(body)),
        },
        Bitvector32Term::PureFunctionApplication { name, arguments } => {
            Bitvector32Term::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(normalize_direct_atomic_memory_load)
                    .collect(),
            }
        }
        Bitvector32Term::MemoryLoad(memory, pointer) => match memory.load(pointer) {
            CExpressionOutcome::Value(CValue::Int32(value) | CValue::UInt8(value))
                if &value != term =>
            {
                normalize_direct_atomic_memory_load(&value)
            }
            _ => Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(canonical_c_memory_for_pointer_load(
                    memory, pointer,
                )),
                Box::new(Pointer {
                    block: pointer.block.clone(),
                    offset: normalize_direct_atomic_pointer_offset_loads(&pointer.offset),
                }),
            ),
        },
    }
}

pub(in crate::lang::click) fn plan_simp_certificate(
    proposition: &Proposition,
    assumptions: &Assumptions,
) -> Option<ProofReplayPlan> {
    let tactic = if matches!(normalize_proposition(proposition), SimpProposition::True) {
        ProofTactic::Normalize
    } else {
        ProofTactic::ExactPropositionDerivation(assumptions.derive_simp_proposition(proposition)?)
    };
    ProofReplayPlan::from_planned_tactics(&[tactic]).ok()
}

pub(in crate::lang::click) fn replay_simp_certificate(
    proposition: &Proposition,
    assumptions: &Assumptions,
    certificate: &ProofReplayPlan,
) -> bool {
    match certificate.tactics() {
        [ProofTactic::Normalize] => {
            matches!(normalize_proposition(proposition), SimpProposition::True)
        }
        [ProofTactic::ExactPropositionDerivation(derivation)] => {
            derivation.conclusion() == proposition && derivation.replay(assumptions)
        }
        _ => false,
    }
}

pub(in crate::lang::click) fn simp_proposition(
    proposition: &Proposition,
    assumptions: &Assumptions,
) -> SimpProposition {
    if let Some(certificate) = plan_simp_certificate(proposition, assumptions)
        && replay_simp_certificate(proposition, assumptions, &certificate)
    {
        return SimpProposition::True;
    }
    let simplified = match proposition {
        Proposition::Equal(left, right) => match simp_terms_equal(left, right) {
            Some(true) => SimpProposition::True,
            Some(false) => SimpProposition::False,
            None => {
                SimpProposition::Proposition(Proposition::Equal(simp_term(left), simp_term(right)))
            }
        },
        Proposition::ConditionIs(condition, expected) => {
            match simp_condition(condition, assumptions) {
                Some(actual) if actual == *expected => SimpProposition::True,
                Some(_) => SimpProposition::False,
                None => SimpProposition::Proposition(proposition.clone()),
            }
        }
        Proposition::And(left, right) => {
            let left = simp_proposition(left, assumptions);
            let right = simp_proposition(right, assumptions);
            match (left, right) {
                (SimpProposition::False, _) | (_, SimpProposition::False) => SimpProposition::False,
                (SimpProposition::True, SimpProposition::True) => SimpProposition::True,
                (SimpProposition::True, right) => right,
                (left, SimpProposition::True) => left,
                (left, right) => SimpProposition::Proposition(Proposition::And(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        Proposition::Or(left, right) => {
            let left = simp_proposition(left, assumptions);
            let right = simp_proposition(right, assumptions);
            match (left, right) {
                (SimpProposition::True, _) | (_, SimpProposition::True) => SimpProposition::True,
                (SimpProposition::False, SimpProposition::False) => SimpProposition::False,
                (SimpProposition::False, right) => right,
                (left, SimpProposition::False) => left,
                (left, right) => SimpProposition::Proposition(Proposition::Or(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        Proposition::Not(body) => match simp_proposition(body, assumptions) {
            SimpProposition::True => SimpProposition::False,
            SimpProposition::False => SimpProposition::True,
            body => {
                SimpProposition::Proposition(Proposition::Not(Box::new(body.into_proposition())))
            }
        },
        Proposition::Implies(left, right) => {
            let left = simp_proposition(left, assumptions);
            let right = simp_proposition(right, assumptions);
            match (left, right) {
                (SimpProposition::False, _) | (_, SimpProposition::True) => SimpProposition::True,
                (SimpProposition::True, right) => right,
                (_, SimpProposition::False) => SimpProposition::False,
                (left, right) => SimpProposition::Proposition(Proposition::Implies(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        Proposition::ForAll { .. }
        | Proposition::Exists { .. }
        | Proposition::Predicate { .. }
        | Proposition::CExpressionEvaluates { .. }
        | Proposition::CConditionEvaluates { .. }
        | Proposition::CStatementExecutes { .. }
        | Proposition::CStatementVerifies { .. }
        | Proposition::CFunctionExecutes { .. }
        | Proposition::CFunctionVerifies { .. }
        | Proposition::CFunctionSatisfiesSpecification { .. }
        | Proposition::CFunctionPartiallySatisfiesSpecification { .. }
        | Proposition::CMemoryLoads { .. }
        | Proposition::CMemoryLoadable { .. }
        | Proposition::CMemoryCanStore { .. }
        | Proposition::CMemoryDisjoint { .. }
        | Proposition::CResourceSeparate { .. }
        | Proposition::CResourceContains { .. }
        | Proposition::CMemoryMutatesOnly { .. }
        | Proposition::CMemoryEffectSummary { .. }
        | Proposition::CHeapLifetimeRetired { .. }
        | Proposition::CWhileInvariantRule { .. } => {
            SimpProposition::Proposition(proposition.clone())
        }
    };
    if matches!(simplified, SimpProposition::True) {
        // A successful smart tactic must come from the certificate path above.
        SimpProposition::Proposition(proposition.clone())
    } else {
        simplified
    }
}

impl SimpProposition {
    fn into_proposition(self) -> Proposition {
        match self {
            Self::True => Proposition::ConditionIs(ConditionTerm::Constant(true), true),
            Self::False => Proposition::ConditionIs(ConditionTerm::Constant(false), true),
            Self::Proposition(proposition) => proposition,
        }
    }
}

pub(in crate::lang::click) fn simp_terms_equal(left: &Term, right: &Term) -> Option<bool> {
    let left = simp_term(left);
    let right = simp_term(right);
    if left == right {
        return Some(true);
    }
    match (&left, &right) {
        (Term::Bitvector32(left), Term::Bitvector32(right)) => Some(
            simp_bitvector_const(&simp_bitvector(left))?
                == simp_bitvector_const(&simp_bitvector(right))?,
        ),
        (Term::Condition(left), Term::Condition(right)) => Some(
            simp_condition_without_assumptions(left)? == simp_condition_without_assumptions(right)?,
        ),
        _ => None,
    }
}

pub(in crate::lang::click) fn simp_term(term: &Term) -> Term {
    match term {
        Term::Condition(condition) => match simp_condition_without_assumptions(condition) {
            Some(value) => Term::Condition(ConditionTerm::Constant(value)),
            None => term.clone(),
        },
        Term::Bitvector32(term) => Term::Bitvector32(simp_bitvector(term)),
        Term::CValue(CValue::Int32(term)) => Term::CValue(CValue::Int32(simp_bitvector(term))),
        _ => term.clone(),
    }
}

pub(in crate::lang::click) fn simp_condition(
    condition: &ConditionTerm,
    assumptions: &Assumptions,
) -> Option<bool> {
    simp_condition_without_assumptions(condition)
        .or_else(|| assumptions.decide_condition_for_simp(condition))
}

pub(in crate::lang::click) fn simp_condition_without_assumptions(
    condition: &ConditionTerm,
) -> Option<bool> {
    match condition {
        ConditionTerm::Constant(value) => Some(*value),
        ConditionTerm::Bitvector32Equal(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                Some(true)
            } else {
                Some(simp_bitvector_const(&left)? == simp_bitvector_const(&right)?)
            }
        }
        ConditionTerm::Bitvector32SignedLessThan(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                Some(false)
            } else {
                Some((simp_bitvector_const(&left)? as i32) < (simp_bitvector_const(&right)? as i32))
            }
        }
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                Some(true)
            } else {
                Some(
                    (simp_bitvector_const(&left)? as i32) <= (simp_bitvector_const(&right)? as i32),
                )
            }
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                Some(false)
            } else {
                Some((simp_bitvector_const(&left)? as i32) > (simp_bitvector_const(&right)? as i32))
            }
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                Some(true)
            } else {
                Some(
                    (simp_bitvector_const(&left)? as i32) >= (simp_bitvector_const(&right)? as i32),
                )
            }
        }
        ConditionTerm::Variable(_)
        | ConditionTerm::Bitvector32SignedAddOverflows(_, _)
        | ConditionTerm::Bitvector32SignedSubtractOverflows(_, _)
        | ConditionTerm::Bitvector32SignedMultiplyOverflows(_, _)
        | ConditionTerm::Bitvector32SignedDivideOverflows(_, _)
        | ConditionTerm::Bitvector32SignedShiftLeftOverflows(_, _)
        | ConditionTerm::PointerOffsetEqual(_, _)
        | ConditionTerm::PointerEqual(_, _) => None,
    }
}

pub(in crate::lang::click) fn simp_bitvector_const(term: &Bitvector32Term) -> Option<u32> {
    match term {
        Bitvector32Term::Constant(value) => Some(*value),
        Bitvector32Term::Variable(_)
        | Bitvector32Term::RangeFold { .. }
        | Bitvector32Term::PureFunctionApplication { .. }
        | Bitvector32Term::MemoryLoad(_, _) => None,
        Bitvector32Term::Add(left, right) => {
            Some(simp_bitvector_const(left)?.wrapping_add(simp_bitvector_const(right)?))
        }
        Bitvector32Term::Subtract(left, right) => {
            Some(simp_bitvector_const(left)?.wrapping_sub(simp_bitvector_const(right)?))
        }
        Bitvector32Term::Multiply(left, right) => {
            Some(simp_bitvector_const(left)?.wrapping_mul(simp_bitvector_const(right)?))
        }
        Bitvector32Term::Divide(left, right) => {
            let left = simp_bitvector_const(left)? as i32;
            let right = simp_bitvector_const(right)? as i32;
            if right == 0 || (left == i32::MIN && right == -1) {
                None
            } else {
                Some((left / right) as u32)
            }
        }
        Bitvector32Term::Remainder(left, right) => {
            let left = simp_bitvector_const(left)? as i32;
            let right = simp_bitvector_const(right)? as i32;
            if right == 0 || (left == i32::MIN && right == -1) {
                None
            } else {
                Some((left % right) as u32)
            }
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            let left = simp_bitvector_const(left)? as i32;
            let right = bitvector32_shift_count(simp_bitvector_const(right)?)?;
            if left < 0 {
                None
            } else {
                let shifted = (left as i64) << right;
                (shifted <= i64::from(i32::MAX)).then_some((shifted as i32) as u32)
            }
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            let left = simp_bitvector_const(left)? as i32;
            let right = bitvector32_shift_count(simp_bitvector_const(right)?)?;
            Some((left >> right) as u32)
        }
        Bitvector32Term::BitwiseAnd(left, right) => {
            Some(simp_bitvector_const(left)? & simp_bitvector_const(right)?)
        }
        Bitvector32Term::BitwiseOr(left, right) => {
            Some(simp_bitvector_const(left)? | simp_bitvector_const(right)?)
        }
        Bitvector32Term::BitwiseXor(left, right) => {
            Some(simp_bitvector_const(left)? ^ simp_bitvector_const(right)?)
        }
        Bitvector32Term::BitwiseNot(value) => Some(!simp_bitvector_const(value)?),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => match simp_condition_without_assumptions(condition)? {
            true => simp_bitvector_const(then_term),
            false => simp_bitvector_const(else_term),
        },
    }
}

pub(in crate::lang::click) fn simp_bitvector(term: &Bitvector32Term) -> Bitvector32Term {
    match term {
        Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => term.clone(),
        Bitvector32Term::Add(left, right) => {
            bitvector32_add(simp_bitvector(left), simp_bitvector(right))
        }
        Bitvector32Term::Subtract(left, right) => {
            bitvector32_subtract(simp_bitvector(left), simp_bitvector(right))
        }
        Bitvector32Term::Multiply(left, right) => {
            bitvector32_multiply(simp_bitvector(left), simp_bitvector(right))
        }
        Bitvector32Term::Divide(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            bitvector32_divide(left.clone(), right.clone())
                .unwrap_or_else(|_| Bitvector32Term::Divide(Box::new(left), Box::new(right)))
        }
        Bitvector32Term::Remainder(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            bitvector32_remainder(left.clone(), right.clone())
                .unwrap_or_else(|_| Bitvector32Term::Remainder(Box::new(left), Box::new(right)))
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            bitvector32_shift_left(left.clone(), right.clone())
                .unwrap_or_else(|_| Bitvector32Term::ShiftLeft(Box::new(left), Box::new(right)))
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            bitvector32_shift_right(left.clone(), right.clone()).unwrap_or_else(|_| {
                Bitvector32Term::ArithmeticShiftRight(Box::new(left), Box::new(right))
            })
        }
        Bitvector32Term::BitwiseAnd(left, right) => {
            bitvector32_and(simp_bitvector(left), simp_bitvector(right))
        }
        Bitvector32Term::BitwiseOr(left, right) => {
            bitvector32_or(simp_bitvector(left), simp_bitvector(right))
        }
        Bitvector32Term::BitwiseXor(left, right) => {
            bitvector32_xor(simp_bitvector(left), simp_bitvector(right))
        }
        Bitvector32Term::BitwiseNot(value) => bitvector32_not(simp_bitvector(value)),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => match simp_condition_without_assumptions(condition) {
            Some(true) => simp_bitvector(then_term),
            Some(false) => simp_bitvector(else_term),
            None => Bitvector32Term::if_then_else(
                condition.as_ref().clone(),
                simp_bitvector(then_term),
                simp_bitvector(else_term),
            ),
        },
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => Bitvector32Term::range_fold(
            simp_bitvector(start),
            simp_bitvector(end),
            simp_bitvector(initial),
            *accumulator,
            *item,
            simp_bitvector(body),
        ),
        Bitvector32Term::PureFunctionApplication { name, arguments } => {
            Bitvector32Term::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments.iter().map(simp_bitvector).collect(),
            }
        }
        Bitvector32Term::MemoryLoad(memory, pointer) => {
            Bitvector32Term::MemoryLoad(memory.clone(), pointer.clone())
        }
    }
}

#[cfg(test)]
mod normalization_tests {
    use super::*;

    #[test]
    fn direct_load_normalization_canonicalizes_loads_inside_the_address() {
        let local = Pointer {
            block: "local:ignored".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before = CMemory::new()
            .with_block("call-havoc:1", 0)
            .with_block("local:ignored", 4)
            .store(local.clone(), CValue::Int32(Bitvector32Term::Constant(1)));
        let after = CMemory::new()
            .with_block("call-havoc:1", 0)
            .with_block("local:ignored", 4)
            .store(local, CValue::Int32(Bitvector32Term::Constant(2)));
        let field = Pointer {
            block: "arg-memory".into(),
            offset: PointerOffsetTerm::Constant(8),
        };
        let dependent_load = |memory: CMemory| {
            let loaded_pointer = Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(memory.clone()),
                Box::new(field.clone()),
            );
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(memory),
                Box::new(Pointer {
                    block: "arg-memory".into(),
                    offset: PointerOffsetTerm::Int32Scaled {
                        value: Box::new(loaded_pointer),
                        byte_width: 4,
                    },
                }),
            )
        };

        assert_eq!(
            normalize_direct_atomic_memory_load(&dependent_load(before)),
            normalize_direct_atomic_memory_load(&dependent_load(after)),
        );
    }
}
