use super::*;

#[derive(Clone)]
struct Link {
    left: SyntaxTerm,
    right: SyntaxTerm,
    strict: bool,
}

impl Link {
    fn from_surface(proposition: &SyntaxProposition) -> Option<Self> {
        let comparison = surface_comparison_with_anchored_operands(proposition);
        let strict = surface_strict_parts(&comparison);
        let (left, right) = strict
            .clone()
            .or_else(|| surface_nonstrict_parts(&comparison))?;
        Some(Self {
            left,
            right,
            strict: strict.is_some(),
        })
    }

    fn surface(&self) -> SyntaxProposition {
        SyntaxProposition::Comparison {
            left: self.left.clone(),
            operator: if self.strict {
                ComparisonOperator::LessThan
            } else {
                ComparisonOperator::LessEqual
            },
            right: self.right.clone(),
        }
    }

    fn gap(left: &SyntaxTerm, right: &SyntaxTerm) -> Option<Self> {
        let left_value = Self::literal(left)?;
        let right_value = Self::literal(right)?;
        (left_value < right_value).then(|| Self {
            left: left.clone(),
            right: right.clone(),
            strict: true,
        })
    }

    fn literal(expression: &SyntaxTerm) -> Option<i32> {
        match expression {
            SyntaxTerm::IntegerLiteral(text) => text.parse().ok(),
            SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int32(term))) => {
                term.constant32().map(|bits| bits as i32)
            }
            SyntaxTerm::At { expression, .. } => Self::literal(expression),
            SyntaxTerm::Negate(inner) => {
                let SyntaxTerm::IntegerLiteral(text) = inner.as_ref() else {
                    return None;
                };
                i32::try_from(text.parse::<i64>().ok()?.checked_neg()?).ok()
            }
            _ => None,
        }
    }
}

fn application(
    name: &str,
    arguments: Vec<SyntaxTerm>,
    premises: Vec<SyntaxProposition>,
) -> ProofStep {
    ProofStep::ApplyPlannedTheorem {
        application: TheoremApplication {
            name: format!("click::integer::{name}"),
            arguments,
        },
        premises,
    }
}

fn retain<'a>(
    proof: Proof<'a>,
    goal: SyntaxProposition,
    step: ProofStep,
) -> Result<Proof<'a>, ClickError> {
    let kernel = proof.lower_surface_proposition(&goal, "signed order bound")?;
    if proof.facts().contains(&kernel) {
        return Ok(proof);
    }
    proof
        .driver()
        .open_have(goal)?
        .driver()
        .apply_step_then_close(step)?
        .join()
}

fn weaken<'a>(proof: Proof<'a>, link: &Link) -> Result<Proof<'a>, ClickError> {
    let goal = Link {
        strict: false,
        ..link.clone()
    };
    retain(
        proof,
        goal.surface(),
        application(
            "int32_less_than_implies_less_equal",
            vec![link.left.clone(), link.right.clone()],
            vec![link.surface()],
        ),
    )
}

/// Compose the already selected path in one direction. A statement's lower
/// bounds usually share their literal lower endpoint; its upper bounds share
/// their upper endpoint. Keeping the intermediate results at the caller's
/// frontier lets the next store cite them, including inside a branch.
fn retain_bounds<'a>(
    input: &Proof<'a>,
    goal: &SyntaxProposition,
    premises: &[SyntaxProposition],
) -> Option<Proof<'a>> {
    let requested = Link::from_surface(goal)?;
    let mut cursor = requested.left.clone();
    let mut links = Vec::new();
    let mut proof = input.clone();
    for link in premises.iter().map(Link::from_surface) {
        let link = link?;
        if let Some(gap) = Link::gap(&cursor, &link.left) {
            proof = retain(proof, gap.surface(), ProofStep::Known).ok()?;
            links.push(gap);
        }
        cursor = link.right.clone();
        links.push(link);
    }
    if let Some(gap) = Link::gap(&cursor, &requested.right) {
        proof = retain(proof, gap.surface(), ProofStep::Known).ok()?;
        links.push(gap);
    }

    // Store lower bounds are non-strict. Keep their reusable prefixes in
    // that form, including when a strict input edge suffices.
    if !requested.strict {
        for link in links.iter_mut().filter(|link| link.strict) {
            proof = weaken(proof, link).ok()?;
            link.strict = false;
        }
    }
    let forward = Link::literal(&requested.left).is_some()
        || links
            .first()
            .is_some_and(|link| Link::literal(&link.left).is_some());
    if !forward {
        links.reverse();
    }
    // The selected kernel path supplies the joins. Surface operands can
    // spell one value at different program points, so the ordinary theorem
    // checker matches the actual premises for each join.
    let mut links = links.into_iter();
    let mut bound = links.next()?;
    for next in links {
        let (mut left, right) = if forward {
            (bound, next)
        } else {
            (next, bound)
        };
        let result = Link {
            left: left.left.clone(),
            right: right.right.clone(),
            strict: left.strict || right.strict,
        };
        let kernel = proof
            .lower_surface_proposition(&result.surface(), "signed order bound")
            .ok()?;
        if !proof.facts().contains(&kernel) {
            if left.strict && right.strict {
                proof = weaken(proof, &left).ok()?;
                left.strict = false;
            }
            let theorem = match (left.strict, right.strict) {
                (true, _) => "int32_less_than_less_equal_transitive",
                (_, true) => "int32_less_equal_less_than_transitive",
                _ => "int32_less_equal_transitive",
            };
            proof = retain(
                proof,
                result.surface(),
                application(
                    theorem,
                    vec![left.left.clone(), left.right.clone(), right.right.clone()],
                    vec![left.surface(), right.surface()],
                ),
            )
            .ok()?;
        }
        bound = result;
    }
    Some(proof)
}

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    pub(in crate::surface::proof) fn retain_signed_order_bounds(
        frontier: &Proof<'a>,
        goal: &SyntaxProposition,
        minimum_edges: usize,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("retain_signed_order_bounds");
        Link::from_surface(goal)?;
        let kernel = frontier
            .lower_surface_proposition(goal, "signed order bound")
            .ok()?;
        if frontier.facts().contains(&kernel) {
            return None;
        }
        let path = crate::kernel::search::ProofSearch::signed_order_chain_premises(
            frontier.facts().assumptions(),
            &kernel,
        )?;
        if path.len() < minimum_edges {
            return None;
        }
        let premises = Self::resolve_solve_premises_unmeasured(frontier, &path, &[])?
            .into_iter()
            .map(|(_, surface)| surface)
            .collect::<Vec<_>>();
        let proof = retain_bounds(frontier, goal, &premises)?;
        retain(proof, goal.clone(), ProofStep::Known).ok()
    }

    pub(super) fn close_selected_signed_order(
        input: &Proof<'a>,
        premises: &[SyntaxProposition],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("close_selected_signed_order");
        let proof = retain_bounds(input, input.surface_goal()?, premises)?;
        if proof.is_complete() {
            Some(proof)
        } else {
            proof.driver().apply_step(ProofStep::Known).ok()
        }
    }
}
