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
    if equality_is_vacuous(equality) {
        return Ok(goal.clone());
    }
    enum RewriteTask<'a> {
        Visit(&'a Proposition),
        BuildAnd,
        BuildOr,
        BuildNot,
        BuildImplies,
        BuildForAll {
            var: Variable,
            sort: Sort,
        },
        BuildExists {
            name: String,
            var: Variable,
            sort: Sort,
        },
    }

    let mut tasks = vec![RewriteTask::Visit(goal)];
    let mut results: Vec<(Proposition, bool)> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            RewriteTask::Visit(proposition) => match proposition {
                Proposition::And(left, right) => {
                    tasks.push(RewriteTask::BuildAnd);
                    tasks.push(RewriteTask::Visit(right));
                    tasks.push(RewriteTask::Visit(left));
                }
                Proposition::Or(left, right) => {
                    tasks.push(RewriteTask::BuildOr);
                    tasks.push(RewriteTask::Visit(right));
                    tasks.push(RewriteTask::Visit(left));
                }
                Proposition::Not(body) => {
                    tasks.push(RewriteTask::BuildNot);
                    tasks.push(RewriteTask::Visit(body));
                }
                Proposition::Implies(antecedent, consequent) => {
                    tasks.push(RewriteTask::BuildImplies);
                    tasks.push(RewriteTask::Visit(consequent));
                    tasks.push(RewriteTask::Visit(antecedent));
                }
                Proposition::ForAll { var, sort, body } => {
                    tasks.push(RewriteTask::BuildForAll {
                        var: *var,
                        sort: sort.clone(),
                    });
                    tasks.push(RewriteTask::Visit(body));
                }
                Proposition::Exists {
                    name,
                    var,
                    sort,
                    body,
                } => {
                    tasks.push(RewriteTask::BuildExists {
                        name: name.clone(),
                        var: *var,
                        sort: sort.clone(),
                    });
                    tasks.push(RewriteTask::Visit(body));
                }
                atomic => {
                    match rewrite_atomic_proposition_by_exact_equality(atomic, equality, available)
                    {
                        Ok(rewritten) => results.push((rewritten, true)),
                        Err(message) if message.contains("does not occur in") => {
                            results.push((atomic.clone(), false));
                        }
                        Err(message) => return Err(message),
                    }
                }
            },
            RewriteTask::BuildAnd | RewriteTask::BuildOr | RewriteTask::BuildImplies => {
                let (right, right_changed) = results.pop().expect("right rewrite result");
                let (left, left_changed) = results.pop().expect("left rewrite result");
                let rewritten = match task {
                    RewriteTask::BuildAnd => Proposition::And(Box::new(left), Box::new(right)),
                    RewriteTask::BuildOr => Proposition::Or(Box::new(left), Box::new(right)),
                    RewriteTask::BuildImplies => {
                        Proposition::Implies(Box::new(left), Box::new(right))
                    }
                    _ => unreachable!(),
                };
                results.push((rewritten, left_changed || right_changed));
            }
            RewriteTask::BuildNot => {
                let (body, changed) = results.pop().expect("negation rewrite result");
                results.push((Proposition::Not(Box::new(body)), changed));
            }
            RewriteTask::BuildForAll { var, sort } => {
                let (body, changed) = results.pop().expect("universal rewrite result");
                results.push((
                    Proposition::ForAll {
                        var,
                        sort,
                        body: Box::new(body),
                    },
                    changed,
                ));
            }
            RewriteTask::BuildExists { name, var, sort } => {
                let (body, changed) = results.pop().expect("existential rewrite result");
                results.push((
                    Proposition::Exists {
                        name,
                        var,
                        sort,
                        body: Box::new(body),
                    },
                    changed,
                ));
            }
        }
    }
    let (rewritten, changed) = results.pop().expect("root rewrite result");
    debug_assert!(results.is_empty());
    return changed
        .then_some(rewritten)
        .ok_or_else(|| "`rewrite` equality does not occur in the current goal".to_string());
}

/// Whether rewriting by this equality cannot change any goal: it states
/// that a term equals itself, or it has already simplified to `true`.
///
/// Both arise when the prover resolves two forms a proof script still
/// distinguishes. The step is then vacuous rather than wrong, so it must not
/// be reported as a missing occurrence or an unsupported equality shape.
fn equality_is_vacuous(equality: &Proposition) -> bool {
    if matches!(
        equality,
        Proposition::ConditionIs(ConditionTerm::Constant(true), true)
    ) {
        return true;
    }
    match equality {
        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) => {
            left == right
        }
        Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(left, right), true) => {
            left == right
        }
        Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), true) => left == right,
        _ => false,
    }
}

/// `rewrite` looks through a load variable: the rewritten term may occur
/// inside the address of the load the variable stands for. Rewriting that
/// address and taking the canonical form of the rewritten load gives the
/// load variable (or recorded value) for the rewritten read — equality
/// substitution is congruent through a load whether the load is written as a
/// term or named by its variable. Deterministic: the registry view and the
/// canonical form are the same on check.
fn rewrite_through_load_variable(
    term: &Bitvector32Term,
    rewrite_pointer: &impl Fn(&Pointer) -> Pointer,
) -> Option<Bitvector32Term> {
    let Bitvector32Term::Variable(variable) = term else {
        return None;
    };
    if !crate::kernel::is_load_variable(variable) {
        return None;
    }
    let (memory, pointer) = crate::kernel::registered_load_for_variable(variable)?;
    let rewritten = rewrite_pointer(&pointer);
    if rewritten == pointer {
        return None;
    }
    Some(crate::kernel::canonical_term(&Bitvector32Term::MemoryLoad(
        memory,
        Box::new(rewritten),
    )))
}

fn rewrite_atomic_proposition_by_exact_equality(
    goal: &Proposition,
    equality: &Proposition,
    available: &[Proposition],
) -> Result<Proposition, String> {
    // Built only if the cheap checks below fail: `rewrite` runs once per
    // tactic, but assembling an assumption context is not free.
    let bridging_assumptions = std::cell::OnceCell::new();
    let is_available = |fact: &Proposition| {
        available.contains(fact)
            || exactly_available_fact(fact, available).is_some()
            // Load variables are kernel-internal. Recorded equalities
            // chained through one are the same user-level fact, and two
            // load variables that framing identifies with one unchanged cell are the
            // same atom, so an equality over either form is available.
            || crate::lang::click::proof::fact_reasoning::premise_bridged_by_load_variable_chain_with_origins(
                fact,
                available,
                bridging_assumptions
                    .get_or_init(|| assumptions_from_propositions(available)),
            )
    };

    if let Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(left, right), true) = equality
    {
        let reverse = Proposition::ConditionIs(
            ConditionTerm::PointerOffsetEqual(
                Box::new(right.as_ref().clone()),
                Box::new(left.as_ref().clone()),
            ),
            true,
        );
        if !is_available(equality) && !is_available(&reverse) {
            return Err(
                "`rewrite` requires its equality to be an exact available fact".to_string(),
            );
        }
        fn rewrite_offset(
            offset: &PointerOffsetTerm,
            left: &PointerOffsetTerm,
            right: &PointerOffsetTerm,
        ) -> PointerOffsetTerm {
            if offset == left
                // Load variables and load terms of one atom are
                // the same occurrence.
                || crate::kernel::offsets_have_same_canonical_form(offset, left)
            {
                return right.clone();
            }
            match offset {
                PointerOffsetTerm::Add(first, second) => PointerOffsetTerm::add(
                    rewrite_offset(first, left, right),
                    rewrite_offset(second, left, right),
                ),
                _ => offset.clone(),
            }
        }
        fn rewrite_term_offset(
            term: &Bitvector32Term,
            left: &PointerOffsetTerm,
            right: &PointerOffsetTerm,
        ) -> Bitvector32Term {
            let rewrite_pointer = |pointer: &Pointer| Pointer {
                block: pointer.block.clone(),
                offset: rewrite_offset(&pointer.offset, left, right),
            };
            let binary = |left_term: &Bitvector32Term, right_term: &Bitvector32Term| {
                (
                    Box::new(rewrite_term_offset(left_term, left, right)),
                    Box::new(rewrite_term_offset(right_term, left, right)),
                )
            };
            match term {
                Bitvector32Term::Add(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::Add(left, right)
                }
                Bitvector32Term::Subtract(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::Subtract(left, right)
                }
                Bitvector32Term::Multiply(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::Multiply(left, right)
                }
                Bitvector32Term::Divide(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::Divide(left, right)
                }
                Bitvector32Term::Remainder(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::Remainder(left, right)
                }
                Bitvector32Term::ShiftLeft(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::ShiftLeft(left, right)
                }
                Bitvector32Term::ArithmeticShiftRight(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::ArithmeticShiftRight(left, right)
                }
                Bitvector32Term::BitwiseAnd(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::BitwiseAnd(left, right)
                }
                Bitvector32Term::BitwiseOr(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::BitwiseOr(left, right)
                }
                Bitvector32Term::BitwiseXor(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::BitwiseXor(left, right)
                }
                Bitvector32Term::BitwiseNot(value) => {
                    Bitvector32Term::BitwiseNot(Box::new(rewrite_term_offset(value, left, right)))
                }
                Bitvector32Term::PureFunctionApplication { name, arguments } => {
                    Bitvector32Term::PureFunctionApplication {
                        name: name.clone(),
                        arguments: arguments
                            .iter()
                            .map(|argument| rewrite_term_offset(argument, left, right))
                            .collect(),
                    }
                }
                Bitvector32Term::MemoryLoad(memory, pointer) => {
                    Bitvector32Term::MemoryLoad(memory.clone(), Box::new(rewrite_pointer(pointer)))
                }
                Bitvector32Term::Variable(_) => {
                    rewrite_through_load_variable(term, &rewrite_pointer)
                        .unwrap_or_else(|| term.clone())
                }
                Bitvector32Term::If { .. }
                | Bitvector32Term::RangeFold { .. }
                | Bitvector32Term::Constant(_) => term.clone(),
            }
        }
        fn rewrite_resource_offset(
            resource: &CResource,
            left: &PointerOffsetTerm,
            right: &PointerOffsetTerm,
        ) -> CResource {
            match resource {
                CResource::Memory(range) => CResource::Memory(CMemoryRange::new(
                    Pointer {
                        block: range.base().block.clone(),
                        offset: rewrite_offset(&range.base().offset, left, right),
                    },
                    rewrite_term_offset(range.start(), left, right),
                    rewrite_term_offset(range.end(), left, right),
                )),
                CResource::Composite { .. } | CResource::Token { .. } => resource.clone(),
            }
        }
        let rewritten = match goal {
            Proposition::ConditionIs(
                ConditionTerm::PointerOffsetEqual(goal_left, goal_right),
                expected,
            ) => Proposition::ConditionIs(
                ConditionTerm::PointerOffsetEqual(
                    Box::new(rewrite_offset(goal_left, left, right)),
                    Box::new(rewrite_offset(goal_right, left, right)),
                ),
                *expected,
            ),
            Proposition::ConditionIs(
                ConditionTerm::PointerEqual(goal_left, goal_right),
                expected,
            ) => {
                let rewrite_pointer = |pointer: &Pointer| Pointer {
                    block: pointer.block.clone(),
                    offset: rewrite_offset(&pointer.offset, left, right),
                };
                Proposition::ConditionIs(
                    ConditionTerm::PointerEqual(
                        Box::new(rewrite_pointer(goal_left)),
                        Box::new(rewrite_pointer(goal_right)),
                    ),
                    *expected,
                )
            }
            Proposition::ConditionIs(condition, expected) => {
                let rewrite_term = |term: &Bitvector32Term| rewrite_term_offset(term, left, right);
                let rewritten = match condition {
                    ConditionTerm::Bitvector32SignedLessThan(left, right) => {
                        ConditionTerm::Bitvector32SignedLessThan(
                            Box::new(rewrite_term(left)),
                            Box::new(rewrite_term(right)),
                        )
                    }
                    ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
                        ConditionTerm::Bitvector32SignedLessEqual(
                            Box::new(rewrite_term(left)),
                            Box::new(rewrite_term(right)),
                        )
                    }
                    ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
                        ConditionTerm::Bitvector32SignedGreaterThan(
                            Box::new(rewrite_term(left)),
                            Box::new(rewrite_term(right)),
                        )
                    }
                    ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
                        ConditionTerm::Bitvector32SignedGreaterEqual(
                            Box::new(rewrite_term(left)),
                            Box::new(rewrite_term(right)),
                        )
                    }
                    ConditionTerm::Bitvector32Equal(left, right) => {
                        ConditionTerm::Bitvector32Equal(
                            Box::new(rewrite_term(left)),
                            Box::new(rewrite_term(right)),
                        )
                    }
                    _ => {
                        return Err(
                            "`rewrite` pointer-offset equality does not occur in this goal"
                                .to_string(),
                        );
                    }
                };
                Proposition::ConditionIs(rewritten, *expected)
            }
            Proposition::CResourceSeparate {
                left: goal_left,
                right: goal_right,
            } => Proposition::CResourceSeparate {
                left: rewrite_resource_offset(goal_left, left, right),
                right: rewrite_resource_offset(goal_right, left, right),
            },
            Proposition::CResourceContains { parent, child } => Proposition::CResourceContains {
                parent: rewrite_resource_offset(parent, left, right),
                child: rewrite_resource_offset(child, left, right),
            },
            _ => {
                return Err(
                    "`rewrite` pointer-offset equality does not occur in this goal".to_string(),
                );
            }
        };
        if &rewritten == goal {
            return Err("`rewrite` equality does not occur in the current goal".to_string());
        }
        return Ok(rewritten);
    }
    if let Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), true) = equality {
        let reverse = Proposition::ConditionIs(
            ConditionTerm::PointerEqual(
                Box::new(right.as_ref().clone()),
                Box::new(left.as_ref().clone()),
            ),
            true,
        );
        if !is_available(equality) && !is_available(&reverse) {
            return Err(
                "`rewrite` requires its equality to be an exact available fact".to_string(),
            );
        }
        let rewrite_pointer = |pointer: &Pointer| {
            if pointer == left.as_ref() {
                right.as_ref().clone()
            } else {
                pointer.clone()
            }
        };
        // A pointer equality also rewrites the subject of a load: replacing
        // the loaded pointer with its proven-equal form is exact term
        // congruence, with work bounded by the goal's size.
        fn rewrite_load_pointers(
            term: &Bitvector32Term,
            rewrite_pointer: &impl Fn(&Pointer) -> Pointer,
        ) -> Bitvector32Term {
            let binary = |left_term: &Bitvector32Term, right_term: &Bitvector32Term| {
                (
                    Box::new(rewrite_load_pointers(left_term, rewrite_pointer)),
                    Box::new(rewrite_load_pointers(right_term, rewrite_pointer)),
                )
            };
            match term {
                Bitvector32Term::MemoryLoad(memory, pointer) => {
                    Bitvector32Term::MemoryLoad(memory.clone(), Box::new(rewrite_pointer(pointer)))
                }
                Bitvector32Term::Variable(_) => {
                    rewrite_through_load_variable(term, rewrite_pointer)
                        .unwrap_or_else(|| term.clone())
                }
                Bitvector32Term::Add(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::Add(left, right)
                }
                Bitvector32Term::Subtract(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::Subtract(left, right)
                }
                Bitvector32Term::Multiply(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::Multiply(left, right)
                }
                Bitvector32Term::Divide(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::Divide(left, right)
                }
                Bitvector32Term::Remainder(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::Remainder(left, right)
                }
                _ => term.clone(),
            }
        }
        let rewritten = match goal {
            Proposition::ConditionIs(
                ConditionTerm::PointerEqual(goal_left, goal_right),
                expected,
            ) => Proposition::ConditionIs(
                ConditionTerm::PointerEqual(
                    Box::new(rewrite_pointer(goal_left)),
                    Box::new(rewrite_pointer(goal_right)),
                ),
                *expected,
            ),
            Proposition::ConditionIs(condition, expected) => {
                let rewrite_term =
                    |term: &Bitvector32Term| rewrite_load_pointers(term, &rewrite_pointer);
                let rewritten = match condition {
                    ConditionTerm::Bitvector32SignedLessThan(goal_left, goal_right) => {
                        ConditionTerm::Bitvector32SignedLessThan(
                            Box::new(rewrite_term(goal_left)),
                            Box::new(rewrite_term(goal_right)),
                        )
                    }
                    ConditionTerm::Bitvector32SignedLessEqual(goal_left, goal_right) => {
                        ConditionTerm::Bitvector32SignedLessEqual(
                            Box::new(rewrite_term(goal_left)),
                            Box::new(rewrite_term(goal_right)),
                        )
                    }
                    ConditionTerm::Bitvector32SignedGreaterThan(goal_left, goal_right) => {
                        ConditionTerm::Bitvector32SignedGreaterThan(
                            Box::new(rewrite_term(goal_left)),
                            Box::new(rewrite_term(goal_right)),
                        )
                    }
                    ConditionTerm::Bitvector32SignedGreaterEqual(goal_left, goal_right) => {
                        ConditionTerm::Bitvector32SignedGreaterEqual(
                            Box::new(rewrite_term(goal_left)),
                            Box::new(rewrite_term(goal_right)),
                        )
                    }
                    ConditionTerm::Bitvector32Equal(goal_left, goal_right) => {
                        ConditionTerm::Bitvector32Equal(
                            Box::new(rewrite_term(goal_left)),
                            Box::new(rewrite_term(goal_right)),
                        )
                    }
                    _ => {
                        return Err(
                            "`rewrite` pointer equality does not occur in this goal".to_string()
                        );
                    }
                };
                Proposition::ConditionIs(rewritten, *expected)
            }
            _ => {
                return Err("`rewrite` pointer equality expects a condition goal".to_string());
            }
        };
        if &rewritten == goal {
            return Err("`rewrite` equality does not occur in the current goal".to_string());
        }
        return Ok(rewritten);
    }
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
    if !is_available(equality) && !is_available(&reverse) {
        return Err("`rewrite` requires its equality to be an exact available fact".to_string());
    }
    fn rewrite_term(
        term: &Bitvector32Term,
        from: &Bitvector32Term,
        to: &Bitvector32Term,
    ) -> Bitvector32Term {
        fn rewrite_offset(
            offset: &PointerOffsetTerm,
            from: &Bitvector32Term,
            to: &Bitvector32Term,
        ) -> PointerOffsetTerm {
            match offset {
                PointerOffsetTerm::Add(left, right) => PointerOffsetTerm::add(
                    rewrite_offset(left, from, to),
                    rewrite_offset(right, from, to),
                ),
                PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                    PointerOffsetTerm::scale_int32(rewrite_term(value, from, to), *byte_width)
                }
                PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => offset.clone(),
            }
        }
        if term == from
            // Load variables and load terms of one atom are the
            // same occurrence.
            || crate::kernel::terms_have_same_canonical_form(term, from)
        {
            return to.clone();
        }
        let binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
            (
                Box::new(rewrite_term(left, from, to)),
                Box::new(rewrite_term(right, from, to)),
            )
        };
        // Substituting a constant can leave a two-constant operation
        // (`0 + 1` after `rewrite(len == 0)` in a `len + 1` goal); folding
        // it is deterministic arithmetic on the rewritten node only, so the
        // rewritten goal states the value the substitution denotes.
        match term {
            Bitvector32Term::Add(left, right) => {
                let (left, right) = binary(left, right);
                match (left.as_ref(), right.as_ref()) {
                    (Bitvector32Term::Constant(first), Bitvector32Term::Constant(second)) => {
                        Bitvector32Term::Constant(first.wrapping_add(*second))
                    }
                    _ => Bitvector32Term::Add(left, right),
                }
            }
            Bitvector32Term::Subtract(left, right) => {
                let (left, right) = binary(left, right);
                match (left.as_ref(), right.as_ref()) {
                    (Bitvector32Term::Constant(first), Bitvector32Term::Constant(second)) => {
                        Bitvector32Term::Constant(first.wrapping_sub(*second))
                    }
                    _ => Bitvector32Term::Subtract(left, right),
                }
            }
            Bitvector32Term::Multiply(left, right) => Bitvector32Term::multiply(
                rewrite_term(left, from, to),
                rewrite_term(right, from, to),
            ),
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
                Bitvector32Term::BitwiseNot(Box::new(rewrite_term(value, from, to)))
            }
            Bitvector32Term::PureFunctionApplication { name, arguments } => {
                Bitvector32Term::PureFunctionApplication {
                    name: name.clone(),
                    arguments: arguments
                        .iter()
                        .map(|argument| rewrite_term(argument, from, to))
                        .collect(),
                }
            }
            // The memory snapshot is fixed, but its address is an ordinary
            // expression: exact equality substitution is congruent there too.
            Bitvector32Term::MemoryLoad(memory, pointer) => Bitvector32Term::MemoryLoad(
                memory.clone(),
                Box::new(Pointer {
                    block: pointer.block.clone(),
                    offset: rewrite_offset(&pointer.offset, from, to),
                }),
            ),
            Bitvector32Term::Variable(_) => {
                rewrite_through_load_variable(term, &|pointer| Pointer {
                    block: pointer.block.clone(),
                    offset: rewrite_offset(&pointer.offset, from, to),
                })
                .unwrap_or_else(|| term.clone())
            }
            Bitvector32Term::If { .. }
            | Bitvector32Term::RangeFold { .. }
            | Bitvector32Term::Constant(_) => term.clone(),
        }
    }

    fn rewrite_offset_term(
        offset: &PointerOffsetTerm,
        from: &Bitvector32Term,
        to: &Bitvector32Term,
    ) -> PointerOffsetTerm {
        match offset {
            PointerOffsetTerm::Add(left, right) => PointerOffsetTerm::add(
                rewrite_offset_term(left, from, to),
                rewrite_offset_term(right, from, to),
            ),
            PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                PointerOffsetTerm::scale_int32(rewrite_term(value, from, to), *byte_width)
            }
            PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => offset.clone(),
        }
    }

    let rewrite_resource_term = |resource: &CResource| match resource {
        CResource::Memory(range) => CResource::Memory(CMemoryRange::new(
            Pointer {
                block: range.base().block.clone(),
                offset: rewrite_offset_term(&range.base().offset, left, right),
            },
            rewrite_term(range.start(), left, right),
            rewrite_term(range.end(), left, right),
        )),
        CResource::Composite { .. } | CResource::Token { .. } => resource.clone(),
    };
    let rewritten = match goal {
        Proposition::ConditionIs(condition, expected) => {
            let rewritten_condition = match condition {
                ConditionTerm::Bitvector32SignedLessThan(goal_left, goal_right) => {
                    ConditionTerm::Bitvector32SignedLessThan(
                        Box::new(rewrite_term(goal_left, left, right)),
                        Box::new(rewrite_term(goal_right, left, right)),
                    )
                }
                ConditionTerm::Bitvector32SignedLessEqual(goal_left, goal_right) => {
                    ConditionTerm::Bitvector32SignedLessEqual(
                        Box::new(rewrite_term(goal_left, left, right)),
                        Box::new(rewrite_term(goal_right, left, right)),
                    )
                }
                ConditionTerm::Bitvector32SignedGreaterThan(goal_left, goal_right) => {
                    ConditionTerm::Bitvector32SignedGreaterThan(
                        Box::new(rewrite_term(goal_left, left, right)),
                        Box::new(rewrite_term(goal_right, left, right)),
                    )
                }
                ConditionTerm::Bitvector32SignedGreaterEqual(goal_left, goal_right) => {
                    ConditionTerm::Bitvector32SignedGreaterEqual(
                        Box::new(rewrite_term(goal_left, left, right)),
                        Box::new(rewrite_term(goal_right, left, right)),
                    )
                }
                ConditionTerm::Bitvector32Equal(goal_left, goal_right) => {
                    ConditionTerm::Bitvector32Equal(
                        Box::new(rewrite_term(goal_left, left, right)),
                        Box::new(rewrite_term(goal_right, left, right)),
                    )
                }
                // Pointer goals contain the same int32 terms inside their
                // offsets; substituting the proven equality there is the same
                // exact term congruence, with work bounded by the goal.
                ConditionTerm::PointerOffsetEqual(goal_left, goal_right) => {
                    ConditionTerm::PointerOffsetEqual(
                        Box::new(rewrite_offset_term(goal_left, left, right)),
                        Box::new(rewrite_offset_term(goal_right, left, right)),
                    )
                }
                ConditionTerm::PointerEqual(goal_left, goal_right) => {
                    let rewrite_pointer = |pointer: &Pointer| Pointer {
                        block: pointer.block.clone(),
                        offset: rewrite_offset_term(&pointer.offset, left, right),
                    };
                    ConditionTerm::PointerEqual(
                        Box::new(rewrite_pointer(goal_left)),
                        Box::new(rewrite_pointer(goal_right)),
                    )
                }
                _ => {
                    return Err("`rewrite` currently expects an int32 comparison goal".to_string());
                }
            };
            Proposition::ConditionIs(rewritten_condition, *expected)
        }
        Proposition::CResourceSeparate {
            left: goal_left,
            right: goal_right,
        } => Proposition::CResourceSeparate {
            left: rewrite_resource_term(goal_left),
            right: rewrite_resource_term(goal_right),
        },
        Proposition::CResourceContains { parent, child } => Proposition::CResourceContains {
            parent: rewrite_resource_term(parent),
            child: rewrite_resource_term(child),
        },
        Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
        } => Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: Pointer {
                block: base.block.clone(),
                offset: rewrite_offset_term(&base.offset, left, right),
            },
            bytes: rewrite_term(bytes, left, right),
        },
        _ => return Err("`rewrite` int32 equality does not occur in this goal".to_string()),
    };
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
    plan_explicit_equality_rewrites_then(goal, premises, available, &|_| None)
}

/// Plan exact equality substitutions, allowing a named simple rule to close
/// the rewritten goal. The closer must itself return explicit tactics; this
/// composes certificate steps rather than adding another proof search.
pub(in crate::lang::click) fn plan_explicit_equality_rewrites_then(
    goal: &Proposition,
    premises: &[(Proposition, ClickProposition)],
    available: &[Proposition],
    closer: &impl Fn(&Proposition) -> Option<Vec<ProofTactic>>,
) -> Option<Vec<ProofTactic>> {
    let exactly_available = |current: &Proposition| available.iter().any(|fact| fact == current);
    plan_explicit_equality_rewrites_from(goal, premises, available, &exactly_available, closer)
}

/// The single explicit-certificate search shared by every smart-simplification
/// construction path. Both the point-proof `simp() using` chain and the
/// post-execution outcome planner must call through here (directly or via
/// [`plan_explicit_equality_rewrites_then`]), so a named simple rule available
/// to one is available to the other. `is_available` is the caller's judgment
/// of when the current goal closes by `assumption`.
pub(in crate::lang::click) fn plan_explicit_equality_rewrites_from(
    goal: &Proposition,
    premises: &[(Proposition, ClickProposition)],
    available: &[Proposition],
    is_available: &impl Fn(&Proposition) -> bool,
    closer: &impl Fn(&Proposition) -> Option<Vec<ProofTactic>>,
) -> Option<Vec<ProofTactic>> {
    fn reverse_equality(
        kernel: &Proposition,
        surface: &ClickProposition,
    ) -> Option<(Proposition, ClickProposition)> {
        let kernel = match kernel {
            Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) => {
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(right.clone(), left.clone()),
                    true,
                )
            }
            Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), true) => {
                Proposition::ConditionIs(
                    ConditionTerm::PointerEqual(right.clone(), left.clone()),
                    true,
                )
            }
            Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(left, right), true) => {
                Proposition::ConditionIs(
                    ConditionTerm::PointerOffsetEqual(right.clone(), left.clone()),
                    true,
                )
            }
            _ => return None,
        };
        let ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            right,
        } = surface
        else {
            return None;
        };
        Some((
            kernel,
            ClickProposition::Comparison {
                left: right.clone(),
                operator: ComparisonOperator::Equal,
                right: left.clone(),
            },
        ))
    }

    fn search(
        current: Proposition,
        premises: &[(Proposition, ClickProposition)],
        available: &[Proposition],
        used: &mut [bool],
        tactics: &mut Vec<ProofTactic>,
        is_available: &impl Fn(&Proposition) -> bool,
        closer: &impl Fn(&Proposition) -> Option<Vec<ProofTactic>>,
    ) -> bool {
        if is_available(&current) {
            tactics.push(ProofTactic::Assumption);
            return true;
        }
        if normalizes_context_free(&current) {
            tactics.push(ProofTactic::Normalize);
            return true;
        }
        if let Some(suffix) = closer(&current) {
            tactics.extend(suffix);
            return true;
        }
        // A disjunction closes the way `left`/`right` check closes it: the
        // selected disjunct must be the same total boolean condition as an
        // available fact up to polarity (`x > 0` from `not (x <= 0)`).
        // Construction mirrors exactly that rule, and commits only
        // when a disjunct closes, so nothing beyond the two children is
        // examined.
        if let Proposition::Or(left_child, right_child) = &current {
            for (tactic, child) in [
                (ProofTactic::Left, left_child.as_ref()),
                (ProofTactic::Right, right_child.as_ref()),
            ] {
                if available
                    .iter()
                    .any(|fact| condition_polarity_equivalent(fact, child))
                {
                    tactics.push(tactic);
                    return true;
                }
            }
        }
        for (index, (kernel, surface)) in premises.iter().enumerate() {
            if used[index] {
                continue;
            }
            let mut orientations = vec![(kernel.clone(), surface.clone())];
            if let Some(reverse) = reverse_equality(kernel, surface) {
                orientations.push(reverse);
            }
            for (oriented_kernel, oriented_surface) in orientations {
                let Ok(rewritten) =
                    rewrite_proposition_by_exact_equality(&current, &oriented_kernel, available)
                else {
                    continue;
                };
                used[index] = true;
                tactics.push(ProofTactic::Rewrite(oriented_surface));
                if search(
                    rewritten,
                    premises,
                    available,
                    used,
                    tactics,
                    is_available,
                    closer,
                ) {
                    return true;
                }
                tactics.pop();
                used[index] = false;
            }
        }
        false
    }

    let mut used = vec![false; premises.len()];
    let mut tactics = Vec::new();
    search(
        goal.clone(),
        premises,
        available,
        &mut used,
        &mut tactics,
        is_available,
        closer,
    )
    .then_some(tactics)
}

/// The checked kernel evidence behind one successful smart simplification.
/// Search produces this at the moment it succeeds and immediately writes it
/// as explicit surface tactics; it is never stored, ordered into a plan, or
/// checked as a private operation program. A derivation the surface
/// vocabulary cannot write is a search failure, not a lowering error.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::lang::click) enum SimpEvidence {
    /// The goal is (an exact equivalent of) an available fact.
    Assumption,
    /// The goal normalizes to true without consulting any context.
    Normalize,
    /// A kernel derivation of the goal from its context premises.
    Derivation(PropositionDerivation),
}

pub(in crate::lang::click) fn plan_simp_certificate(
    proposition: &Proposition,
    assumptions: &PureFactContext,
) -> Option<SimpEvidence> {
    if matches!(normalize_proposition(proposition), SimpProposition::True) {
        Some(SimpEvidence::Normalize)
    } else {
        Some(SimpEvidence::Derivation(
            assumptions.derive_simp_proposition(proposition)?,
        ))
    }
}

pub(in crate::lang::click) fn check_simp_certificate(
    proposition: &Proposition,
    assumptions: &PureFactContext,
    certificate: &SimpEvidence,
) -> bool {
    match certificate {
        SimpEvidence::Assumption => assumptions.proves(proposition),
        SimpEvidence::Normalize => {
            matches!(normalize_proposition(proposition), SimpProposition::True)
        }
        SimpEvidence::Derivation(derivation) => {
            derivation.conclusion() == proposition && derivation.check(assumptions)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rewrite_uses_pointer_offset_equalities_inside_pointer_goals() {
        let left = PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(41))),
            byte_width: 4,
        };
        let right = PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(42))),
            byte_width: 4,
        };
        let equality = Proposition::ConditionIs(
            ConditionTerm::PointerOffsetEqual(Box::new(left.clone()), Box::new(right.clone())),
            true,
        );
        let pointer = |offset| Pointer {
            block: PointerBlock::ExternalArgument,
            offset,
        };
        let null = Pointer {
            block: "null".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let goal = Proposition::ConditionIs(
            ConditionTerm::pointer_equal(pointer(left), null.clone()),
            true,
        );

        assert_eq!(
            rewrite_proposition_by_exact_equality(
                &goal,
                &equality,
                std::slice::from_ref(&equality),
            )
            .unwrap(),
            Proposition::ConditionIs(ConditionTerm::pointer_equal(pointer(right), null), true,),
        );
    }

    #[test]
    fn rewrite_substitutes_index_and_base_equalities_inside_load_addresses() {
        let memory = crate::kernel::intern_c_memory(CMemory::new());
        let data = Bitvector32Term::Variable(Variable(51));
        let alias = Bitvector32Term::Variable(Variable(52));
        let index = Bitvector32Term::Variable(Variable(53));
        let pointer = |offset| Pointer {
            block: PointerBlock::ExternalArgument,
            offset,
        };
        let load = |offset| Bitvector32Term::MemoryLoad(memory.clone(), Box::new(pointer(offset)));
        let data_offset = PointerOffsetTerm::scale_int32(data.clone(), 4);
        let alias_offset = PointerOffsetTerm::scale_int32(alias.clone(), 4);
        let indexed_offset = PointerOffsetTerm::add(
            data_offset.clone(),
            PointerOffsetTerm::scale_int32(index.clone(), 4),
        );
        let goal = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(load(indexed_offset)),
                Box::new(load(alias_offset.clone())),
            ),
            true,
        );
        let index_is_zero = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(index),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        );
        let data_is_alias = Proposition::ConditionIs(
            ConditionTerm::PointerOffsetEqual(Box::new(data_offset), Box::new(alias_offset)),
            true,
        );
        let available = [index_is_zero.clone(), data_is_alias.clone()];

        let indexed =
            rewrite_proposition_by_exact_equality(&goal, &index_is_zero, &available).unwrap();
        let aliased =
            rewrite_proposition_by_exact_equality(&indexed, &data_is_alias, &available).unwrap();
        assert_eq!(normalize_proposition(&aliased), SimpProposition::True);
    }

    #[test]
    fn rewrite_substitutes_length_and_base_equalities_inside_memory_resources() {
        let source = Bitvector32Term::Variable(Variable(61));
        let target = Bitvector32Term::Variable(Variable(62));
        let source_len = Bitvector32Term::Variable(Variable(63));
        let target_len = Bitvector32Term::Variable(Variable(64));
        let fixed = CResource::Memory(CMemoryRange::new(
            Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(65)), 4),
            },
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(4),
        ));
        let range = |base: Bitvector32Term, end: Bitvector32Term| {
            CResource::Memory(CMemoryRange::new(
                Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::scale_int32(base, 4),
                },
                Bitvector32Term::Constant(0),
                end,
            ))
        };
        let goal = Proposition::CResourceSeparate {
            left: fixed.clone(),
            right: range(source.clone(), source_len.clone()),
        };
        let length_equality = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(Box::new(source_len), Box::new(target_len.clone())),
            true,
        );
        let base_equality = Proposition::ConditionIs(
            ConditionTerm::PointerOffsetEqual(
                Box::new(PointerOffsetTerm::scale_int32(source, 4)),
                Box::new(PointerOffsetTerm::scale_int32(target.clone(), 4)),
            ),
            true,
        );
        let available = [length_equality.clone(), base_equality.clone()];

        let resized =
            rewrite_proposition_by_exact_equality(&goal, &length_equality, &available).unwrap();
        let replaced =
            rewrite_proposition_by_exact_equality(&resized, &base_equality, &available).unwrap();
        assert_eq!(
            replaced,
            Proposition::CResourceSeparate {
                left: fixed,
                right: range(target, target_len),
            }
        );
    }
}

pub(in crate::lang::click) fn simp_proposition(
    proposition: &Proposition,
    assumptions: &PureFactContext,
) -> SimpProposition {
    if let Some(certificate) = plan_simp_certificate(proposition, assumptions)
        && check_simp_certificate(proposition, assumptions, &certificate)
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
        | Proposition::CResourceComposition(_)
        | Proposition::CResourceContains { .. }
        | Proposition::CMemoryMutatesOnly { .. }
        | Proposition::CMemoryEffectSummary { .. }
        | Proposition::CHeapAllocationFreed { .. }
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
    assumptions: &PureFactContext,
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
