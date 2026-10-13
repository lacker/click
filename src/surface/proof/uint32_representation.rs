use super::*;

fn equality_arguments(
    proposition: &ClickProposition,
) -> Option<(ContractExpression, ContractExpression)> {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            right,
        } => Some((left.clone(), right.clone())),
        ClickProposition::At {
            selector,
            proposition,
        } => {
            let (left, right) = equality_arguments(proposition)?;
            Some((
                ContractExpression::At {
                    selector: selector.clone(),
                    expression: Box::new(left),
                },
                ContractExpression::At {
                    selector: selector.clone(),
                    expression: Box::new(right),
                },
            ))
        }
        _ => None,
    }
}

/// Spell the retained byte observations through a selected live local at
/// its recorded snapshot. The caller checks each candidate's exact lowering.
pub(super) fn byte_premises_at_snapshot(
    derivation: &PropositionDerivation,
    parameter_binding: ParameterBinding<'_>,
    state: &CState,
    anchor: &ProgramPointRef,
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let (word, premises) = derivation.uint32_representation_premises()?;
    // The retained word keeps its live snapshot and source address. Its
    // load variable may instead name a projection before initialization.
    let raw = super::surface_synthesis::synthesize_surface_machine_expression(
        word,
        parameter_binding,
        state,
    );
    let ContractExpression::CFragment(CExpression::Variable(local)) = raw? else {
        return None;
    };
    let object = CExpression::AddressOf(Box::new(CExpression::Variable(local)));
    let bytes = crate::kernel::c_cast(object.clone(), CType::UInt8Pointer);
    let byte_view = ContractExpression::CUnary {
        operand: Box::new(ContractExpression::CFragment(object)),
        lowered: bytes.clone(),
    };
    premises
        .iter()
        .enumerate()
        .map(|(byte, premise)| {
            let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) =
                premise
            else {
                return None;
            };
            let value = left.as_const().or_else(|| right.as_const())?;
            let value = u8::try_from(value).ok()?;
            let address = crate::kernel::c_pointer_offset_bytes(bytes.clone(), byte as u32);
            let surface_address = if byte == 0 {
                byte_view.clone()
            } else {
                ContractExpression::CUnary {
                    operand: Box::new(byte_view.clone()),
                    lowered: address.clone(),
                }
            };
            Some((
                premise.clone(),
                ClickProposition::At {
                    selector: SnapshotSelector::ProgramPoint(anchor.clone()),
                    proposition: Box::new(ClickProposition::Comparison {
                        left: ContractExpression::CUnary {
                            operand: Box::new(surface_address),
                            lowered: crate::kernel::c_typed_load(address, CType::UInt8),
                        },
                        operator: ComparisonOperator::Equal,
                        right: ContractExpression::CFragment(CExpression::Value(
                            crate::kernel::uint8(u32::from(value)),
                        )),
                    }),
                },
            ))
        })
        .collect()
}

pub(super) fn plan_recorded_uint32_representation(
    goal: &Proposition,
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
    surface_goal: &ClickProposition,
    application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let (word, premises) = derivation.uint32_representation_premises()?;
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) = goal else {
        return None;
    };
    let (surface_left, surface_right) = equality_arguments(surface_goal)?;
    let arguments = if left.as_ref() == word {
        vec![surface_left, surface_right]
    } else if right.as_ref() == word {
        vec![surface_right, surface_left]
    } else {
        return None;
    };
    let premises = premises
        .iter()
        .map(|premise| {
            premise_pairs
                .iter()
                .find_map(|(kernel, surface)| (kernel == premise).then(|| surface.clone()))
        })
        .collect::<Option<Vec<_>>>()?;
    let mut tactics = vec![ProofTactic::ApplyTheoremUsing {
        application: TheoremApplication {
            name: "declared_uint32_from_bytes".into(),
            arguments,
        },
        premises,
    }];
    if !application_closes_goal {
        tactics.push(ProofTactic::Assumption);
    }
    Some(tactics)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn instantiate_declared_uint32_from_bytes(
    application: &TheoremApplication,
    claim_label: &str,
    path_index: Option<usize>,
    tactic_index: usize,
    available: &[Proposition],
    assumptions: &PureFactContext,
    context: &theorem_application::TheoremApplicationContext<'_>,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Vec<Proposition>, ClickError> {
    let error = |message: String| {
        theorem_application::theorem_application_error(
            claim_label,
            path_index,
            tactic_index,
            message,
        )
    };
    let [word, value] = application.arguments.as_slice() else {
        return Err(error(
            "declared_uint32_from_bytes expects a word and its constant value".into(),
        ));
    };
    let evaluate = |argument| {
        evaluate_contract_expression_with_environment(
            context.values,
            context.array_refs,
            context.pre_state,
            context.post_state,
            context.result,
            assumptions,
            argument,
            spec_definitions,
            context.recorded_snapshots,
            &mut BTreeSet::new(),
        )
    };
    let CValue::UInt32(word) = evaluate(word).map_err(error)? else {
        return Err(error(
            "declared_uint32_from_bytes requires a uint32 observation".into(),
        ));
    };
    let CValue::UInt32(value) = evaluate(value).map_err(error)? else {
        return Err(error(
            "declared_uint32_from_bytes requires a uint32 constant".into(),
        ));
    };
    let value = value
        .as_const()
        .ok_or_else(|| error("declared_uint32_from_bytes requires a constant result".into()))?;
    let theorem =
        crate::kernel::prove_declared_uint32_from_bytes(word, value).ok_or_else(|| {
            error(
                "the selected uint32 observation has no initialized declared representation".into(),
            )
        })?;
    let Proposition::Implies(guard, conclusion) = theorem.proposition() else {
        return Err(error(
            "the uint32 packing rule must retain its four byte premises".into(),
        ));
    };
    let mut required = Vec::new();
    theorem_application::collect_conjunctive_guard_facts(guard, &mut required);
    if required.len() != 4
        || required
            .iter()
            .any(|premise| !exact_fact_is_available(premise, available))
    {
        return Err(error("declared_uint32_from_bytes requires all four exact byte values from the selected observation".into()));
    }
    Ok(vec![conclusion.as_ref().clone()])
}

#[cfg(test)]
mod tests {

    fn using_body(tactic: &str) -> (usize, usize, Vec<usize>) {
        let start = tactic
            .find("using {")
            .expect("packing cites its four premises")
            + "using {".len();
        let mut nested = 0usize;
        let mut separators = Vec::new();
        for (offset, character) in tactic[start..].char_indices() {
            match character {
                '}' if nested == 0 => return (start, start + offset, separators),
                '(' | '[' | '{' => nested += 1,
                ')' | ']' | '}' => nested -= 1,
                ';' if nested == 0 => separators.push(start + offset),
                _ => {}
            }
        }
        panic!("the explicit premise list closes");
    }

    fn omit_last_using_premise(tactic: &str) -> String {
        let (_, end, separators) = using_body(tactic);
        assert_eq!(
            separators.len(),
            4,
            "packing cites four distinct byte values"
        );
        format!("{}{}", &tactic[..separators[2] + 1], &tactic[end..])
    }

    #[test]
    fn declared_uint32_from_bytes_modular_word_expands_and_checks_retained_premises() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests/modular_byte_output_word_value_requires_representation.md");
        let fixture =
            crate::cli::parse_mdtest(&path, &std::fs::read_to_string(&path).unwrap()).unwrap();
        let source = fixture.click_source.unwrap();
        let sources = fixture
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        crate::surface::verify_c0_sources(&source, &sources).unwrap();
        let expanded = crate::surface::expand_c0_claim_source(
            &source,
            &sources,
            "word",
            crate::surface::CProofClaim::Grouped,
        )
        .unwrap();
        let start = expanded
            .find("apply(declared_uint32_from_bytes")
            .expect("expansion transcribes the guarded packing law");
        let (_, body_end, _) = using_body(&expanded[start..]);
        let end = start + body_end + 1;
        let tactic = &expanded[start..end];
        assert!(
            !tactic.contains("UInt8Pointer"),
            "casts keep their public source spelling: {tactic}"
        );
        assert!(
            tactic.contains("at("),
            "the byte premises keep the snapshot of the retired local: {tactic}"
        );
        crate::surface::verify_c0_sources(&expanded, &sources).unwrap();
        let position = crate::surface::expansion::position_at_offset(&expanded, start);
        let (session, _) = crate::surface::C0VerificationSession::new(&source, &sources).unwrap();
        for _ in 0..2 {
            session
                .verify_at(&expanded, position.line, position.column)
                .unwrap();
        }
        let missing = expanded.replacen(tactic, &omit_last_using_premise(tactic), 1);
        session
            .verify_at(&missing, position.line, position.column)
            .expect_err("ambient byte facts cannot replace an omitted explicit packing premise");
        let changed_byte = tactic.replace("86u8", "87u8");
        assert_ne!(
            changed_byte, tactic,
            "the certificate keeps the byte's source value"
        );
        let changed = expanded.replacen(tactic, &changed_byte, 1);
        session
            .verify_at(&changed, position.line, position.column)
            .expect_err("a mutated byte premise cannot certify the word");
        let changed_goal = expanded.replace("305419896u32", "305419897u32");
        session
            .verify_at(&changed_goal, position.line, position.column)
            .expect_err("the four original bytes cannot certify a changed packed result");
        session
            .verify_at(&expanded, position.line, position.column)
            .unwrap();
    }
}
