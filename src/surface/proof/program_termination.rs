//! Program termination is an ordinary proposition proof with checked, replayable steps.
use super::*;
use crate::kernel::{
    OrdinaryTerminationScope, TerminationCause, TerminationCheck, TerminationCheckReport,
    TerminationRefusal,
};
use crate::persistent::PersistentMap;

#[derive(Clone, Default)]
pub(super) struct TerminationDiagnostics {
    local: PersistentMap<String, Option<TerminationRefusal>>,
    strict: PersistentMap<String, TerminationRefusal>,
    normal: PersistentMap<String, TerminationRefusal>,
    unjustified: PersistentMap<String, ()>,
    callbacks: Arc<Vec<crate::kernel::UnsuitableCallback>>,
}

impl TerminationDiagnostics {
    pub(super) fn extend(&mut self, report: TerminationCheckReport) {
        for (name, refusal) in report.local {
            self.local.insert(name, refusal);
        }
        for (name, strict, cause) in report.functions {
            let refusal = match cause {
                None => continue,
                Some(TerminationCause::Refusal(refusal)) => refusal,
                Some(TerminationCause::Local { function, call }) => {
                    match self.local.get(&function).and_then(Clone::clone) {
                        Some(refusal @ TerminationRefusal::UnrankedLoop { .. }) => refusal,
                        local => call
                            .or(local)
                            .unwrap_or(TerminationRefusal::Callee { callee: function }),
                    }
                }
            };
            if strict {
                self.strict.insert(name, refusal);
            } else {
                self.normal.insert(name, refusal);
            }
        }
        for name in report.unjustified {
            self.unjustified.insert(name, ());
        }
        if !report.callbacks.is_empty() {
            self.callbacks = Arc::new(report.callbacks);
        }
    }

    pub(super) fn failure(
        &self,
        scope: &OrdinaryTerminationScope,
        goal: &Proposition,
    ) -> Option<crate::kernel::ProgramContractFailure> {
        use crate::kernel::{ProgramContractGoal, TerminationAtomKind};
        let mut selected = None;
        let mut fallback = None;
        let mut pending = vec![goal];
        while let Some(goal) = pending.pop() {
            match goal {
                Proposition::And(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                _ => {
                    if let Some((kind, name)) = scope.spelling(goal) {
                        match kind {
                            TerminationAtomKind::Divergence
                                if self.unjustified.get(&name).is_some()
                                    && scope.declared_diverging.contains(&name) =>
                            {
                                selected =
                                    Some((ProgramContractGoal::DivergencePolicy(name), false));
                                break;
                            }
                            TerminationAtomKind::Callbacks if !self.callbacks.is_empty() => {
                                selected = Some((ProgramContractGoal::CallbackSafety, true));
                                break;
                            }
                            TerminationAtomKind::Returns | TerminationAtomKind::Strict => {
                                let strict = kind == TerminationAtomKind::Strict;
                                let refusals = if strict { &self.strict } else { &self.normal };
                                if let Some(refusal) = refusals.get(&name) {
                                    let candidate = (ProgramContractGoal::Returns(name), strict);
                                    if !matches!(refusal, TerminationRefusal::Callee { .. }) {
                                        selected = Some(candidate);
                                        break;
                                    }
                                    fallback.get_or_insert(candidate);
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
        let (goal, strict) = selected.or(fallback)?;
        let source = if strict { &self.strict } else { &self.normal };
        let mut refusals = BTreeMap::new();
        let mut current = match &goal {
            ProgramContractGoal::Returns(name) => Some(name.clone()),
            ProgramContractGoal::CallbackSafety => {
                self.callbacks.first().map(|site| site.callback.clone())
            }
            _ => None,
        };
        // This is the chain the diagnostic prints, selected by exact lookups;
        // unrelated earlier proof results are never enumerated.
        while let Some(name) = current.take() {
            if refusals.contains_key(&name) {
                break;
            }
            let Some(refusal) = source.get(&name) else {
                break;
            };
            if let TerminationRefusal::Callee { callee } = refusal {
                current = Some(callee.clone());
            }
            refusals.insert(name, refusal.clone());
        }
        Some(crate::kernel::ProgramContractFailure::Obligation {
            verdicts: Box::new(crate::kernel::TerminationVerdicts {
                rules: vec![],
                refusals,
                unjustified_diverging: vec![],
                unsuitable_callbacks: self.callbacks.first().cloned().into_iter().collect(),
            }),
            goal,
        })
    }
}

pub(super) fn spelling(scope: &OrdinaryTerminationScope, goal: &Proposition) -> ClickProposition {
    if let Some((kind, name)) = scope.spelling(goal) {
        return ClickProposition::PredicateCall {
            name: kind.spelling().to_string(),
            arguments: if kind == crate::kernel::TerminationAtomKind::Callbacks {
                vec![]
            } else {
                vec![ContractExpression::Binding(name)]
            },
        };
    }
    match goal {
        Proposition::And(left, right) => ClickProposition::And(
            Box::new(spelling(scope, left)),
            Box::new(spelling(scope, right)),
        ),
        Proposition::Not(inner) => ClickProposition::Not(Box::new(spelling(scope, inner))),
        _ => unreachable!("termination producer creates only scoped atoms and conjunctions"),
    }
}

pub(in crate::surface) fn prove(
    generated: crate::kernel::ProgramTerminationProof,
    tactics: Option<&[ProofTactic]>,
    definitions: SpecDefinitions<'_>,
    theorems: &TheoremEnvironment,
    tactic_names: &BTreeSet<String>,
) -> Result<(crate::kernel::ProvedProgramContracts, ProofCertificate), ClickError> {
    let scope = generated.into_ordinary_scope();
    let surface_goal = spelling(&scope, scope.goal());
    let context = pure_theorems::PureTheoremContext {
        diagnostic_names: Arc::from([]),
        declaration_bindings: BTreeMap::new(),
        point: crate::kernel::ProgramPoint::starting_at(&SymbolicMemory::new()),
        values: ProgramValueBindings::new(),
        integer_values: Default::default(),
        array_refs: Default::default(),
        requires: vec![],
        surface_requirements: Default::default(),
    };
    let definitions = definitions.with_termination_scope(&scope, tactic_names);
    let root =
        Proof::for_program_termination(&scope, &surface_goal, &context, definitions, theorems);
    let _claim = implicit_solve_scope::ClaimScope::enter("program.termination");
    let mut search = attempt::search_scope("program termination proof");
    let proof = if let Some(tactics) = tactics {
        let sites = pure_theorems::claim_script_sites(&root, tactics, 0);
        let mut unfinished = None;
        match root.driver().try_addressed_linear_script(
            tactics,
            &sites,
            &mut None,
            Some(&mut unfinished),
            true,
        )? {
            Some(proof) => proof,
            None => solve_omitted(&unfinished.unwrap_or(root), true)?,
        }
    } else {
        solve_omitted(&root, false)?
    };
    search.succeed();
    proof.record_accepted_trace("program.termination", 0);
    let certificate = proof.completed_certificate()?;
    let completed = proof.finish_program_termination()?;
    Ok((completed, certificate))
}

fn solve_omitted<'a>(root: &Proof<'a>, written_block: bool) -> Result<Proof<'a>, ClickError> {
    if implicit_solve_scope::selected_claim_is_strict()
        || (written_block && proof_object::implicit_solve_disabled())
    {
        return Err(root.step_error("termination proof ended with an open goal; write its proof or expand `program.termination`"));
    }
    let _timing = TacticTiming::new("program.termination", 0, 0, &ProofTactic::Solve, 0);
    let _origin = crate::surface::proof_trace::TraceOrigin::enter_implicit("implicit tail");
    crate::kernel::search::ProofSearch::try_solve_closure(root)?.ok_or_else(|| root.solve_failure())
}

pub(super) fn try_closure<'a>(root: &Proof<'a>) -> Result<Option<Proof<'a>>, ClickError> {
    let Some(scope) = root.termination_scope() else {
        return Ok(None);
    };
    let Some(goal) = root.goal() else {
        return Ok(None);
    };
    let plan = crate::surface::planning::solve::plan_termination(scope, goal, root.facts())?;
    if plan.is_empty() {
        return match failure_error(root) {
            Some(error) => Err(error),
            None => Ok(None),
        };
    }
    let mut proof = root.clone();
    for step in plan {
        check_verification_deadline()?;
        let step = match step {
            TerminationCheck::Local(function) => ProofStep::CheckTerminationLocal(function),
            TerminationCheck::Component { function, strict } => {
                ProofStep::CheckTerminationComponent { function, strict }
            }
            TerminationCheck::Callbacks => ProofStep::CheckTerminationCallbacks,
        };
        proof = proof.driver().apply_step(step)?;
    }
    match proof.driver().apply_step(ProofStep::Known) {
        Ok(closed) => Ok(Some(closed)),
        Err(_) => {
            if let Some(error) = failure_error(&proof) {
                return Err(error);
            }
            Err(proof.solve_failure())
        }
    }
}
fn failure_error(proof: &Proof<'_>) -> Option<ClickError> {
    let failure = proof.termination_failure()?;
    let scope = proof
        .termination_scope()
        .expect("termination diagnostic owns its scope");
    Some(
        proof.attach_step_diagnostic(crate::surface::verification::program_contract_failure(
            failure,
            &scope.declared_diverging,
            proof.termination_tactic_names(),
        )),
    )
}

pub(in crate::surface) fn predicate_spelling(name: &str) -> Option<ClickProposition> {
    let (kind, function) = crate::kernel::termination_predicate_spelling(name)?;
    Some(ClickProposition::PredicateCall {
        name: kind.spelling().into(),
        arguments: if kind == crate::kernel::TerminationAtomKind::Callbacks {
            vec![]
        } else {
            vec![ContractExpression::Binding(function.to_string())]
        },
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    const C: &str = "int32 leaf(void) { return 7; } int32 caller(void) { return leaf(); }";
    const SOURCE: &str = "verifying \"termination.c\"; int32 leaf() { ensures result == 7; } int32 caller() { ensures result == 7; }";

    #[test]
    fn targeted_proofs_check_termination_for_their_selected_bodies() {
        let sources = [("termination.c", C)];
        let inputs = ProgramInputs::Bundle(sources.to_vec());
        let source = crate::surface::expand_claim_by_label(
            None,
            SOURCE,
            &inputs,
            "program.termination",
            None,
        )
        .unwrap()
        .source;
        for claim in ["leaf.ensures_0", "caller.ensures_0"] {
            let rewritten = expand_c_claim_source_by_label(&source, &sources, claim).unwrap();
            let at = tactic_source_position(&rewritten, &inputs, claim, 0).unwrap();
            check_audit_claim(claim, true, || {
                verify_c_sources_at(&rewritten, &sources, at.line, at.column)
                    .map_err(|error| error.report())
            })
            .unwrap();
            let (session, _) = ProgramVerificationSession::new(&source, &sources).unwrap();
            session.verify_at(&rewritten, at.line, at.column).unwrap();
        }
        let at = tactic_source_position(&source, &inputs, "program.termination", 0).unwrap();
        let invalid = source.replace(
            "check_termination_local(\"leaf\")",
            "check_termination_local(\"missing\")",
        );
        assert_ne!(invalid, source);
        let error = verify_c_sources_at(&invalid, &sources, at.line, at.column).unwrap_err();
        assert!(error.report().contains("missing"), "{error}");
    }

    #[test]
    fn explicit_termination_uses_ordinary_have_and_solve() {
        let source = format!(
            r#"{SOURCE}
termination by {{
    have termination_returns("leaf") by {{
        check_termination_local("leaf");
        check_termination_component("leaf", normal);
        close();
    }}
    close();
}}
"#
        );
        verify_c_sources(&source, &[("termination.c", C)]).unwrap();
        let expansion = crate::surface::expand_claim_by_label(
            None,
            &source,
            &ProgramInputs::Bundle(vec![("termination.c", C)]),
            "program.termination",
            None,
        )
        .unwrap();
        assert_eq!(
            expansion
                .source
                .matches("check_termination_local(\"leaf\")")
                .count(),
            1,
            "the caller must use the callee promise proved by have"
        );
    }

    #[test]
    fn a_quantified_value_does_not_capture_a_quoted_function_label() {
        let source = format!(
            r#"{SOURCE}
termination by {{
    have forall (leaf: int32) {{ termination_returns("leaf") }} by {{ intro(); close(); }}
    close();
}}
"#
        );
        verify_c_sources(&source, &[("termination.c", C)]).unwrap();
    }

    #[test]
    fn expansion_replays_without_implicit_termination_solving() {
        let inputs = ProgramInputs::Bundle(vec![("termination.c", C)]);
        let expansion = crate::surface::expand_claim_by_label(
            None,
            SOURCE,
            &inputs,
            "program.termination",
            None,
        )
        .unwrap();
        assert!(
            expansion
                .source
                .contains("check_termination_local(\"leaf\")")
        );
        assert!(
            expansion
                .source
                .contains("check_termination_component(\"caller\", normal)")
        );
        let result = crate::surface::without_proof_search_for_claim("program.termination", || {
            verify_c_sources(&expansion.source, &[("termination.c", C)])
                .map_err(|error| error.report())
        });
        result.unwrap();
        let again = crate::surface::expand_claim_by_label(
            None,
            &expansion.source,
            &inputs,
            "program.termination",
            None,
        )
        .unwrap();
        verify_c_sources(&again.source, &[("termination.c", C)]).unwrap();
    }

    #[test]
    fn ordinary_termination_trace_has_source_spellings_and_locations() {
        let inputs = ProgramInputs::Bundle(vec![("termination.c", C)]);
        let expansion = crate::surface::expand_claim_by_label(
            None,
            SOURCE,
            &inputs,
            "program.termination",
            None,
        )
        .unwrap();
        let position =
            tactic_source_position(&expansion.source, &inputs, "program.termination", 0).unwrap();
        let claim = claim_at(
            None,
            &expansion.source,
            &inputs,
            position.line,
            Some(position.column),
            ClaimLocationScope::Innermost,
        )
        .unwrap();
        assert_eq!(claim.label, "program.termination");
        with_proof_trace("program.termination", || {
            verify_c_sources(&expansion.source, &[("termination.c", C)]).unwrap();
            let trace = accepted_proof_trace(&|_, _| None, &|_, _, _| None, &|_, _, _| false, None)
                .unwrap();
            assert!(trace.contains("termination_returns(\"leaf\")"), "{trace}");
            assert!(
                !trace.contains('\0'),
                "scope identities must not leak into a trace"
            );
        });
    }

    #[test]
    fn unrelated_have_does_not_complete_the_program_root() {
        let source = format!("{SOURCE}\ntermination by {{ have true by close(); }}");
        let error = without_implicit_solve_for_claim("program.termination", || {
            verify_c_sources(&source, &[("termination.c", C)]).map_err(|error| error.report())
        })
        .unwrap_err();
        assert!(error.contains("open goal"), "{error}");
    }

    #[test]
    fn termination_steps_cannot_be_used_in_an_ordinary_theorem() {
        let source =
            "theorem forged() { ensures true by { check_termination_callbacks(); close(); } }";
        let error = verify_click_theorems(source).unwrap_err();
        assert!(
            error.report().contains("termination proof"),
            "{}",
            error.report()
        );
    }

    #[test]
    fn unknown_checked_termination_component_is_a_source_error() {
        let source = format!(
            r#"{SOURCE}
termination by {{ check_termination_component("missing", normal); }}
"#
        );
        let error = verify_c_sources(&source, &[("termination.c", C)]).unwrap_err();
        assert!(
            error
                .report()
                .contains("not part of this termination proof"),
            "{}",
            error.report()
        );
    }

    #[test]
    fn termination_atoms_cannot_be_assumed_in_an_ordinary_contract() {
        let source = "theorem forged() { requires termination_returns(\"leaf\"); ensures true; }";
        assert!(verify_click_theorems(source).is_err());
    }
}
