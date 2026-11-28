//! Search exposes historical endpoint equalities as ordinary, explicit facts.
use super::*;

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    /// Name the individual effects that a selected indexed read survived.
    /// Every proposed footprint separation and preservation is checked in
    /// an ordinary have. The final equality checks the goal's actual points.
    pub(in crate::surface::proof) fn try_indexed_read_preservation(
        search_input: &Proof<'a>,
        target: &SyntaxProposition,
        point_limit: usize,
        derive_separation: bool,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_indexed_read_preservation");
        let SyntaxProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            right,
        } = target
        else {
            return Ok(None);
        };
        let outcome = search_input.focused_outcome_data().is_some();
        let (current, returned) = match (left, right) {
            (
                current,
                SyntaxTerm::Old(saved)
                | SyntaxTerm::At {
                    expression: saved, ..
                },
            )
            | (
                SyntaxTerm::Old(saved)
                | SyntaxTerm::At {
                    expression: saved, ..
                },
                current,
            ) if current == saved.as_ref() => (current, false),
            (_, SyntaxTerm::Old(read))
                if outcome && crate::surface::proposition_names_result(target) =>
            {
                (read.as_ref(), true)
            }
            _ => return Ok(None),
        };
        let Some(ProgramExpression::Index(base, index)) =
            contract_expression_as_program_expression(current)
        else {
            return Ok(None);
        };
        let Some(view) = search_input.premise_fixed_state_view() else {
            return Ok(None);
        };
        let records = view.fixed_state.recorded_states;
        let kept = ResourceSubject::SavedMemory {
            base: SyntaxTerm::ProgramExpression(*base),
            start: SyntaxTerm::ProgramExpression(*index),
            end: None,
        };
        let have = |proposition, step| ProofStep::Have {
            proposition,
            proof: Box::new(
                ProofCertificate::from_steps(vec![step]).expect("an ordinary preservation step"),
            ),
        };
        let mut proof = search_input.clone();
        for (selector, _) in records.recent(point_limit) {
            check_verification_deadline()?;
            let ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region,
                kind: ProgramPointKind::Exit,
            }) = selector
            else {
                continue;
            };
            let loop_exit = match region {
                CodeRegionRef::Loop(_) => true,
                CodeRegionRef::Region(index) if returned => {
                    search_input.execution_context().is_some_and(|context| {
                        context
                            .constants
                            .source_layout
                            .loop_index_at_header(*index)
                            .is_some()
                    })
                }
                _ => false,
            };
            if !matches!(region, CodeRegionRef::Region(_) | CodeRegionRef::Path(_))
                && !(returned && loop_exit)
            {
                continue;
            }
            let Ok(Resource::Footprint(footprint)) = records.footprint(region) else {
                continue;
            };
            if !footprint.complete || footprint.members.is_empty() {
                continue;
            }
            let separation = SyntaxProposition::Separate {
                left: ResourceSubject::Footprint(region.clone()),
                right: kept.clone(),
            };
            let at = |kind| SyntaxTerm::At {
                selector: ProgramPointSelector::ProgramPoint(ProgramPointRef {
                    region: region.clone(),
                    kind,
                }),
                expression: Box::new(current.clone()),
            };
            let equality = SyntaxProposition::Comparison {
                left: at(ProgramPointKind::Exit),
                operator: ComparisonOperator::Equal,
                right: at(ProgramPointKind::Entry),
            };
            let separated = attempt::candidate_outcome(
                proof
                    .driver()
                    .apply_step(have(separation.clone(), ProofStep::Known)),
            )?;
            let separated = match separated {
                Some(separated) => Some(separated),
                None if (outcome || derive_separation) && footprint.members.len() == 1 => {
                    let written = footprint.members.front().expect("one footprint member");
                    if !loop_exit
                        && let Some(separated) = Self::try_distinct_indexed_store_separation(
                            &proof,
                            written,
                            &kept,
                            &separation,
                        )?
                    {
                        Some(separated)
                    } else if returned || derive_separation {
                        attempt::candidate_outcome(Self::try_memory_footprint_separation(
                            &proof,
                            &footprint,
                            &kept,
                            &separation,
                        ))?
                        .flatten()
                    } else {
                        None
                    }
                }
                None => None,
            };
            let Some(separated) = separated else {
                continue;
            };
            let candidate = separated
                .driver()
                .apply_step(have(equality, ProofStep::Preserve(separation)));
            if let Some(preserved) = attempt::candidate_outcome(candidate)? {
                if preserved.focused_discharged() {
                    return Ok(Some(preserved));
                }
                if let Some(closed) =
                    attempt::candidate_outcome(preserved.driver().apply_step(ProofStep::Known))?
                {
                    return Ok(Some(closed));
                }
                proof = preserved;
            }
        }
        Ok(None)
    }

    /// For a symbolic single-element store, the index inequality can prove
    /// separation directly. The footprint check ties the written element to
    /// the recorded store before its read equality is used.
    pub(in crate::surface::proof) fn try_distinct_indexed_store_separation(
        search_input: &Proof<'a>,
        written: &Resource,
        kept: &ResourceSubject,
        footprint_separation: &SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_distinct_indexed_store_separation");
        let Resource::Memory(written) = written else {
            return Ok(None);
        };
        let Some(width) = written.single_element_width() else {
            return Ok(None);
        };
        let ResourceSubject::SavedMemory {
            base,
            start: read_index,
            end: None,
        } = kept
        else {
            return Ok(None);
        };
        let Some(view) = search_input.premise_fixed_state_view() else {
            return Ok(None);
        };
        let Some(ProgramExpression::Variable(base_name)) =
            contract_expression_as_program_expression(base)
        else {
            return Ok(None);
        };
        let binding = view.parameter_binding;
        let state = view.fixed_state.state;
        let pointer = state
            .locals()
            .get(&base_name)
            .and_then(|value| value.pointer())
            .or_else(|| {
                let position = binding.index?.position(base_name.source_name())?;
                let ProgramExpression::Value(ProgramValue::Pointer(pointer)) =
                    binding.arguments.get(position)?
                else {
                    return None;
                };
                Some(pointer)
            });
        let Some(pointer) = pointer else {
            return Ok(None);
        };
        if pointer
            .program_type()
            .pointee_type()
            .map(ProgramType::byte_width)
            != Some(width)
        {
            return Ok(None);
        }
        let Some(index) = written
            .base()
            .element_index_from_base_with_width(pointer.address(), width)
        else {
            return Ok(None);
        };
        let Some(write_index) =
            super::super::surface_synthesis::synthesize_surface_machine_expression(
                &index, binding, state,
            )
        else {
            return Ok(None);
        };
        let separation = SyntaxProposition::Separate {
            left: ResourceSubject::SavedMemory {
                base: base.clone(),
                start: write_index.clone(),
                end: None,
            },
            right: kept.clone(),
        };
        let compare =
            |left: &SyntaxTerm, operator, right: &SyntaxTerm| SyntaxProposition::Comparison {
                left: left.clone(),
                operator,
                right: right.clone(),
            };
        let distinct = compare(read_index, ComparisonOperator::NotEqual, &write_index);
        let separate_elements = ProofCertificate::from_steps(vec![
            ProofStep::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "click::separation::separate_elements".into(),
                    arguments: vec![base.clone(), write_index.clone(), read_index.clone()],
                },
                premises: vec![distinct.clone()],
            },
            ProofStep::Known,
        ])
        .expect("ordinary indexed separation");
        let separated = attempt::candidate_outcome(
            search_input
                .driver()
                .apply_have_step(&separation, &separate_elements),
        )?;
        let proof = match separated {
            Some(proof) => Some(proof),
            None => {
                let strict_orders = [
                    compare(&write_index, ComparisonOperator::LessThan, read_index),
                    compare(read_index, ComparisonOperator::LessThan, &write_index),
                ];
                let Some(proof) = Self::try_index_disequality_from_order(
                    search_input,
                    &distinct,
                    compare(&write_index, ComparisonOperator::Equal, read_index),
                    strict_orders,
                )?
                else {
                    return Ok(None);
                };
                attempt::candidate_outcome(
                    proof
                        .driver()
                        .apply_have_step(&separation, &separate_elements),
                )?
            }
        };
        let Some(proof) = proof else {
            return Ok(None);
        };
        let certificate = ProofCertificate::from_steps(vec![ProofStep::Known])
            .expect("ordinary footprint separation");
        attempt::candidate_outcome(
            proof
                .driver()
                .apply_have_step(footprint_separation, &certificate),
        )
    }

    /// A strict comparison refutes equality of the two selected indices.
    fn try_index_disequality_from_order(
        search_input: &Proof<'a>,
        distinct: &SyntaxProposition,
        equality: SyntaxProposition,
        orders: [SyntaxProposition; 2],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_index_disequality_from_order");
        let known =
            ProofCertificate::from_steps(vec![ProofStep::Known]).expect("ordinary order lookup");
        let refute_order = ProofCertificate::from_steps(vec![
            ProofStep::Rewrite(equality.clone()),
            ProofStep::Known,
        ])
        .expect("ordinary refutation of an irreflexive order");
        for order in orders {
            let Some(proof) =
                attempt::candidate_outcome(search_input.driver().apply_have_step(&order, &known))?
                    .or_else(|| Self::retain_signed_order_bounds(search_input, &order, 2))
            else {
                continue;
            };
            let equal_case = ProofCertificate::from_steps(vec![
                ProofStep::Have {
                    proposition: SyntaxProposition::Not(Box::new(order.clone())),
                    proof: Box::new(refute_order.clone()),
                },
                ProofStep::Known,
            ])
            .expect("ordinary refutation of equal indices");
            let proof_steps = ProofCertificate::from_steps(vec![ProofStep::If {
                condition: equality.clone(),
                ensuring: None,
                then_proof: Box::new(equal_case),
                else_proof: Box::new(known.clone()),
            }])
            .expect("ordinary index disequality");
            let checked = || {
                let scope = proof.driver().open_have_as_written(distinct.clone())?;
                scope
                    .driver()
                    .try_authoritative_linear_script(&proof_steps.to_proof_tactics())?
                    .map(|done| done.join())
                    .transpose()
            };
            if let Some(Some(proof)) = attempt::candidate_outcome(checked())? {
                return Ok(Some(proof));
            }
        }
        Ok(None)
    }

    /// Prove separation for each recorded write before checking separation
    /// from the complete footprint.
    pub(in crate::surface::proof) fn try_memory_footprint_separation(
        search_input: &Proof<'a>,
        footprint: &crate::kernel::RegionFootprint,
        kept: &ResourceSubject,
        footprint_separation: &SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_memory_footprint_separation");
        let Some(view) = search_input.premise_fixed_state_view() else {
            return Ok(None);
        };
        let _recorded_points = super::super::surface_synthesis::SynthesisRecordedPointsScope::enter(
            view.fixed_state.recorded_states,
        );
        let known = ProofCertificate::from_steps(vec![ProofStep::Known])
            .expect("ordinary footprint separation");
        let mut proof = search_input.clone();
        for member in &footprint.members {
            check_verification_deadline()?;
            crate::instrumentation::record_deterministic_work(1);
            if !matches!(member, Resource::Memory(_)) {
                return Ok(None);
            }
            let Some(written) =
                super::super::surface_synthesis::synthesize_surface_resource_subject(
                    member,
                    view.parameter_binding,
                    view.fixed_state.state,
                    &std::collections::BTreeMap::new(),
                )
            else {
                return Ok(None);
            };
            let separation = SyntaxProposition::Separate {
                left: written,
                right: kept.clone(),
            };
            if let Some(checked) =
                attempt::candidate_outcome(proof.driver().apply_have_step(&separation, &known))?
            {
                proof = checked;
                continue;
            }
            let Some(goal) =
                attempt::candidate_outcome(proof.driver().open_have(separation.clone()))?
            else {
                return Ok(None);
            };
            let Some(separated) = goal
                .driver()
                .try_indexed_separation_restriction(&separation)?
            else {
                return Ok(None);
            };
            if !separated.is_complete() {
                return Ok(None);
            }
            proof = separated.join()?;
        }
        attempt::candidate_outcome(proof.driver().apply_have_step(footprint_separation, &known))
    }

    /// Use the named store to preserve the exact field observation across
    /// its two endpoints. A struct's field resource can include padding,
    /// so use the byte extent of the load selected by the checked goal.
    pub(in crate::surface::proof) fn try_anchored_field_preservation(
        search_input: &Proof<'a>,
        target: &SyntaxProposition,
        address: &crate::kernel::Address,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_anchored_field_preservation");
        let SyntaxProposition::Comparison {
            left:
                SyntaxTerm::At {
                    selector: ProgramPointSelector::ProgramPoint(left),
                    expression: left_read,
                },
            operator: ComparisonOperator::Equal,
            right:
                SyntaxTerm::At {
                    selector: ProgramPointSelector::ProgramPoint(right),
                    expression: right_read,
                },
        } = target
        else {
            return Ok(None);
        };
        if left.region != right.region
            || left_read != right_read
            || !matches!(left_read.as_ref(), SyntaxTerm::Field { .. })
        {
            return Ok(None);
        }
        let (exit, entry) = match (left.kind, right.kind) {
            (ProgramPointKind::Exit, ProgramPointKind::Entry) => (left, right),
            (ProgramPointKind::Entry, ProgramPointKind::Exit) => (right, left),
            _ => return Ok(None),
        };
        let Some(view) = search_input.premise_fixed_state_view() else {
            return Ok(None);
        };
        let Ok(Resource::Footprint(footprint)) =
            view.fixed_state.recorded_states.footprint(&exit.region)
        else {
            return Ok(None);
        };
        if !footprint.complete || footprint.members.len() != 1 {
            return Ok(None);
        }
        let observation = Resource::Memory(crate::kernel::MemoryRange::new_with_element_width(
            address.clone(),
            0u32.into(),
            1u32.into(),
            4,
        ));
        let Some(kept) = super::super::surface_synthesis::synthesize_surface_resource_subject(
            &observation,
            view.parameter_binding,
            view.fixed_state.state,
            &std::collections::BTreeMap::new(),
        ) else {
            return Ok(None);
        };
        let separation = SyntaxProposition::Separate {
            left: ResourceSubject::Footprint(exit.region.clone()),
            right: kept.clone(),
        };
        let Some(proof) =
            Self::try_memory_footprint_separation(search_input, &footprint, &kept, &separation)?
        else {
            return Ok(None);
        };
        let at = |point: &ProgramPointRef| SyntaxTerm::At {
            selector: ProgramPointSelector::ProgramPoint(point.clone()),
            expression: left_read.clone(),
        };
        let equality = SyntaxProposition::Comparison {
            left: at(exit),
            operator: ComparisonOperator::Equal,
            right: at(entry),
        };
        let preserve = ProofCertificate::from_steps(vec![ProofStep::Preserve(separation)])
            .expect("ordinary field preservation");
        attempt::candidate_outcome(proof.driver().apply_ordinary_transport_steps(
            target,
            vec![
                ProofStep::Have {
                    proposition: equality,
                    proof: Box::new(preserve),
                },
                ProofStep::Known,
            ],
        ))
    }

    /// Supply containment for separation restriction from the introduced
    /// bounds or the reflexive containment law.
    pub(in crate::surface::proof) fn indexed_containment_step(
        goal: &SyntaxProposition,
    ) -> Option<ProofStep> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("indexed_containment_step");
        let SyntaxProposition::Contains { parent, child } = goal else {
            return None;
        };
        if parent == child {
            return Some(ProofStep::ApplyTheorem(TheoremApplication {
                name: "click::separation::contains_refl".into(),
                arguments: vec![SyntaxTerm::Resource(Box::new(parent.clone()))],
            }));
        }
        let ResourceSubject::SavedMemory {
            base,
            start: index,
            end: None,
        } = child
        else {
            return None;
        };
        let (lo, hi) = match parent {
            ResourceSubject::Memory(ContractSegment {
                surface: ContractSegmentSurface::Range { start, end, .. },
                ..
            })
            | ResourceSubject::SavedMemory {
                start,
                end: Some(end),
                ..
            } => (start, end),
            _ => return None,
        };
        Some(ProofStep::ApplyTheoremUsing {
            application: TheoremApplication {
                name: "click::separation::contains_element".into(),
                arguments: vec![base.clone(), lo.clone(), hi.clone(), index.clone()],
            },
            premises: vec![
                SyntaxProposition::Comparison {
                    left: lo.clone(),
                    operator: ComparisonOperator::LessEqual,
                    right: index.clone(),
                },
                SyntaxProposition::Comparison {
                    left: index.clone(),
                    operator: ComparisonOperator::LessThan,
                    right: hi.clone(),
                },
            ],
        })
    }

    /// Discover already recorded footprint separations only in smart search.
    /// The resulting proof applies explicit preservation at each endpoint;
    /// replay neither enumerates facts nor follows memory history.
    pub(in crate::surface::proof) fn try_recorded_footprint_preservation(
        search_input: &Proof<'a>,
        source: &SyntaxProposition,
        target: &SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_recorded_footprint_preservation");
        if preservation_read(source, target).is_none() {
            return Ok(None);
        }
        let Some(spellings) = search_input.context_surface_propositions() else {
            return Ok(None);
        };
        let mut premises = Vec::new();
        for fact in search_input.facts().propositions() {
            check_verification_deadline()?;
            crate::instrumentation::record_deterministic_work(1);
            let Proposition::ResourceSeparate { left, .. } = fact else {
                continue;
            };
            if !matches!(left.as_ref(), crate::kernel::Resource::Footprint(_)) {
                continue;
            }
            let premise = spellings.surface(fact)?;
            if preservation_separation_matches(source, target, premise)
                && !premises.contains(premise)
            {
                premises.push(premise.clone());
            }
        }
        let Some(steps) = statement_preservation_steps(source, target, &premises) else {
            return Ok(None);
        };
        attempt::candidate_outcome(
            search_input
                .driver()
                .apply_ordinary_transport_steps(target, steps),
        )
    }

    pub(in crate::surface::proof) fn try_history_indexed_equalities(
        search_input: &Proof<'a>,
        source: &SyntaxProposition,
        target: &SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_history_indexed_equalities");
        if search_input.surface_goal() != Some(target)
            || old_reflexive_transport_source(target).as_ref() != Some(source)
        {
            return Ok(None);
        }
        let SyntaxProposition::Comparison {
            left: read,
            operator: ComparisonOperator::Equal,
            right: SyntaxTerm::Old(old),
        } = target
        else {
            return Ok(None);
        };
        if read != old.as_ref() {
            return if crate::surface::proposition_names_result(target) {
                Self::try_returned_index_preservation(search_input, target, old)
            } else {
                Ok(None)
            };
        }
        if !matches!(
            contract_expression_as_program_expression(read),
            Some(ProgramExpression::Index(..))
        ) {
            return Ok(None);
        }
        let Some(view) = search_input.premise_fixed_state_view() else {
            return Ok(None);
        };
        let records = view.fixed_state.recorded_states;
        let mut proof = search_input.clone();
        for (selector, _) in records.iter() {
            check_verification_deadline()?;
            let ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: region @ CodeRegionRef::Region(_),
                kind: ProgramPointKind::Entry,
            }) = selector
            else {
                continue;
            };
            let exit = ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: region.clone(),
                kind: ProgramPointKind::Exit,
            });
            if records.get(&exit).is_none() {
                continue;
            }
            let at = |selector| SyntaxTerm::At {
                selector,
                expression: Box::new(read.clone()),
            };
            let equality = SyntaxProposition::Comparison {
                left: at(exit),
                operator: ComparisonOperator::Equal,
                right: at(selector.clone()),
            };
            // Expose the selected endpoint terms to ordinary equality reasoning.
            // No premise or memory history is reconstructed during replay.
            let candidate = (|| {
                let scope = proof.driver().open_have_as_written(equality)?;
                scope.driver().apply_step(ProofStep::Known)?.join()
            })();
            if let Some(unchanged) = attempt::candidate_outcome(candidate)? {
                proof = unchanged;
            }
        }
        attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))
    }

    /// Choose a recorded write and a stated separation for a returned indexed
    /// read. The selected write is checked again through its named footprint;
    /// the final `known` checks that this equality actually closes the result.
    fn try_returned_index_preservation(
        search_input: &Proof<'a>,
        target: &SyntaxProposition,
        read: &SyntaxTerm,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_returned_index_preservation");
        let Some(ProgramExpression::Index(base, index)) =
            contract_expression_as_program_expression(read)
        else {
            return Ok(None);
        };
        let kept = ResourceSubject::SavedMemory {
            base: SyntaxTerm::ProgramExpression(*base),
            start: SyntaxTerm::ProgramExpression(*index),
            end: None,
        };
        let (Some(view), Some(spellings)) = (
            search_input.premise_fixed_state_view(),
            search_input.context_surface_propositions(),
        ) else {
            return Ok(None);
        };
        let records = view.fixed_state.recorded_states;
        let have = |proposition, step| ProofStep::Have {
            proposition,
            proof: Box::new(
                ProofCertificate::from_steps(vec![step]).expect("an ordinary preservation step"),
            ),
        };
        for (selector, _) in records.iter() {
            check_verification_deadline()?;
            let ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: region @ CodeRegionRef::Region(_),
                kind: ProgramPointKind::Entry,
            }) = selector
            else {
                continue;
            };
            let Ok(Resource::Footprint(recorded)) = records.footprint(region) else {
                continue;
            };
            let Some(written @ Resource::Memory(written_range)) = recorded.members.front() else {
                continue;
            };
            if !recorded.complete || recorded.members.len() != 1 {
                continue;
            }
            let footprint = SyntaxProposition::Separate {
                left: ResourceSubject::Footprint(region.clone()),
                right: kept.clone(),
            };
            let Some(lowered) = attempt::candidate_outcome(
                search_input.lower_surface_proposition_direct(&footprint, "preserved cell"),
            )?
            else {
                continue;
            };
            let mut split = &lowered;
            while let Proposition::And(stated, _) = split {
                split = stated;
            }
            let Proposition::ResourceSeparate { right, .. } = split else {
                continue;
            };
            let Some(candidates) = search_input
                .facts()
                .assumptions()
                .resource_separation_candidates(written, right)
            else {
                continue;
            };
            for candidate in candidates {
                check_verification_deadline()?;
                crate::instrumentation::record_deterministic_work(1);
                let Proposition::ResourceSeparate { left, right } = candidate else {
                    continue;
                };
                let Some(mut surface) = spellings.recorded_requirement_surface(candidate) else {
                    continue;
                };
                while let SyntaxProposition::At { proposition, .. } = surface {
                    surface = proposition;
                }
                let SyntaxProposition::Separate {
                    left: left_surface,
                    right: right_surface,
                } = surface
                else {
                    continue;
                };
                let same_storage = |resource: &Resource| {
                    matches!(resource, Resource::Memory(range)
                        if range.base().base == written_range.base().base)
                };
                let covering = if same_storage(left) {
                    left_surface
                } else if same_storage(right) {
                    right_surface
                } else {
                    continue;
                };
                let separation = SyntaxProposition::Separate {
                    left: covering.clone(),
                    right: kept.clone(),
                };
                let at = |kind| SyntaxTerm::At {
                    selector: ProgramPointSelector::ProgramPoint(ProgramPointRef {
                        region: region.clone(),
                        kind,
                    }),
                    expression: Box::new(read.clone()),
                };
                let equality = SyntaxProposition::Comparison {
                    left: at(ProgramPointKind::Exit),
                    operator: ComparisonOperator::Equal,
                    right: at(ProgramPointKind::Entry),
                };
                let steps = vec![
                    have(separation, ProofStep::Known),
                    have(footprint.clone(), ProofStep::Known),
                    have(equality, ProofStep::Preserve(footprint.clone())),
                    ProofStep::Known,
                ];
                if let Some(proof) = attempt::candidate_outcome(
                    search_input
                        .driver()
                        .apply_ordinary_transport_steps(target, steps),
                )? {
                    return Ok(Some(proof));
                }
            }
        }
        Ok(None)
    }
}
