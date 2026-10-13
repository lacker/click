//! Checked observations of one declared uint32 object's representation.
//!
//! The target profile belongs to the immutable declaration in the selected
//! snapshot. Observations neither grant an access nor initialize any byte.

use super::*;

fn selected_object(
    memory: &CMemory,
    address: &Pointer,
    value_type: CType,
) -> Option<(Pointer, u32, UInt32RepresentationProfile)> {
    let byte = u32::try_from(address.offset.as_const()?).ok()?;
    if !matches!(value_type, CType::UInt8 | CType::UInt32)
        || byte >= 4
        || value_type == CType::UInt32 && byte != 0
    {
        return None;
    }
    let object = Pointer {
        block: address.block.clone(),
        offset: PointerOffsetTerm::Constant(0),
    };
    crate::instrumentation::record_deterministic_work(1);
    let profile = memory.declared_uint32_representation(&object)?;
    Some((object, byte, profile))
}

pub(in crate::kernel) fn project_byte(word: Bitvector32Term, byte: u32) -> Bitvector32Term {
    debug_assert!(byte < 4);
    Bitvector32Term::bitwise_and(
        Bitvector32Term::logical_shift_right(word, (8 * byte).into()),
        255u32.into(),
    )
}

pub(in crate::kernel) fn pack_bytes(bytes: [Bitvector32Term; 4]) -> Bitvector32Term {
    bytes
        .into_iter()
        .enumerate()
        .fold(0u32.into(), |word, (byte, bits)| {
            Bitvector32Term::bitwise_or(
                word,
                Bitvector32Term::unsigned_shift_left(
                    Bitvector32Term::bitwise_and(bits, 255u32.into()),
                    (8 * byte as u32).into(),
                ),
            )
        })
}

fn materialized_word(memory: &CMemory, object: &Pointer) -> Option<Bitvector32Term> {
    if let Some(CValue::UInt32(word)) = memory.known_value(object) {
        return Some(canonical_term(&word));
    }
    let mut bytes = Vec::with_capacity(4);
    for byte in 0..4 {
        crate::instrumentation::record_deterministic_work(1);
        let value = memory.known_value(&object.offset_by_bytes(byte))?;
        let bits = match value {
            CValue::UInt8(bits) | CValue::Int8(bits) => bits,
            _ => return None,
        };
        bytes.push(bits);
    }
    Some(pack_bytes(bytes.try_into().ok()?))
}

fn initialized_span(memory: &CMemory, address: &Pointer, bytes: u32) -> bool {
    // A cached cell records a write as well as a value. Constant selected
    // spans need only their initialization runs or overlapping written cells.
    memory.has_initialized_bytes_under(address, bytes, &PureFactContext::new())
}

/// One guarded observation, shared by program and logical load paths. The
/// caller retains its own permission and definedness checks for program reads.
pub(in crate::kernel) fn observe_value(
    memory: &CMemory,
    address: &Pointer,
    value_type: CType,
    symbolic: bool,
) -> Option<CValue> {
    let (object, byte, _) = selected_object(memory, address, value_type)?;
    if !initialized_span(memory, address, value_type.byte_width()) {
        return None;
    }
    if !symbolic
        && value_type == CType::UInt8
        && let Some(CValue::UInt8(bits) | CValue::Int8(bits)) = memory.known_value(address)
    {
        return Some(CValue::UInt8(Bitvector32Term::bitwise_and(
            bits,
            255u32.into(),
        )));
    }
    let word = (!symbolic)
        .then(|| materialized_word(memory, &object))
        .flatten()
        .unwrap_or_else(|| super::memory_loads::canonical_declared_uint32_word(memory, &object));
    Some(if value_type == CType::UInt32 {
        CValue::UInt32(word)
    } else {
        CValue::UInt8(project_byte(word, byte))
    })
}

/// Names the selected virtual word without attributing a typed word access to
/// a source expression that may only read one character.
pub(in crate::kernel) fn record_observation_definition(value: &CValue, facts: &mut ExecutionFacts) {
    let word = match value {
        CValue::UInt32(word) => word,
        CValue::UInt8(Bitvector32Term::BitwiseAnd(bits, mask)) if mask.as_const() == Some(255) => {
            match bits.as_ref() {
                Bitvector32Term::LogicalShiftRight(word, _) => word.as_ref(),
                word => word,
            }
        }
        _ => return,
    };
    if let Bitvector32Term::Variable(variable) = word
        && UInt32PackingEvidence::word_origin(word).is_some()
        && let Some(origin) = registered_load_origin_term_for_variable(variable)
    {
        super::memory_loads::record_load_variable_defining_fact(*variable, origin, facts);
    }
}

impl UInt32PackingEvidence {
    fn word_origin(word: &Bitvector32Term) -> Option<(SharedCMemory, Pointer)> {
        let load = match word {
            Bitvector32Term::Variable(variable)
                if registered_load_kind_for_variable(variable) == Some(LoadKind::Bits32)
                    && registered_load_bytes_for_variable(variable) == Some(4) =>
            {
                registered_load_origin_term_for_variable(variable)?
            }
            Bitvector32Term::MemoryLoad(memory, object, LoadKind::Bits32)
                if super::memory_loads::recorded_load_access_width(memory, object) == Some(4) =>
            {
                word.clone()
            }
            _ => return None,
        };
        let Bitvector32Term::MemoryLoad(memory, object, LoadKind::Bits32) = load else {
            return None;
        };
        Some((memory, *object))
    }

    pub(in crate::kernel) fn for_equality(
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        [(left, right), (right, left)]
            .into_iter()
            .find_map(|(word, result)| {
                let result = result.as_const()?;
                let (memory, object) = Self::word_origin(word)?;
                let (_, _, profile) = selected_object(&memory, &object, CType::UInt32)?;
                if !initialized_span(&memory, &object, 4) {
                    return None;
                }
                // Program reads may retain the live load while logical byte
                // observations name its assumption-free canonical variable.
                // Preserve the live snapshot for declaration and initialization.
                let observation_word = canonical_term(word);
                let mut bytes = Vec::with_capacity(4);
                let mut byte_equalities = Vec::with_capacity(4);
                for byte in 0..4 {
                    let observation = project_byte(observation_word.clone(), byte);
                    let value = (result >> (8 * byte)) as u8;
                    crate::instrumentation::record_deterministic_work(1);
                    // Exact premises can retain a named load application or
                    // its canonical variable. Select only spellings of this
                    // word; canonicalization is assumption-free and does not
                    // transport an observation across an intervening write.
                    let mut words = vec![observation_word.clone()];
                    if let Bitvector32Term::Variable(variable) = &observation_word {
                        if let Some((snapshot, address)) = registered_load_for_variable(variable) {
                            words.push(Bitvector32Term::MemoryLoad(
                                snapshot,
                                Box::new(address),
                                LoadKind::Bits32,
                            ));
                        }
                        if let Some(origin) = registered_load_origin_term_for_variable(variable) {
                            words.push(origin);
                        }
                    }
                    let premise = words.into_iter().find_map(|candidate| {
                        let observed = project_byte(candidate, byte);
                        if canonical_term(&observed) != observation {
                            return None;
                        }
                        let forward = Proposition::ConditionIs(
                            ConditionTerm::equal(observed.clone(), u32::from(value).into()),
                            true,
                        );
                        let backward = Proposition::ConditionIs(
                            ConditionTerm::equal(u32::from(value).into(), observed),
                            true,
                        );
                        [forward, backward]
                            .into_iter()
                            .find(|premise| assumptions.contains_assumed_exact(premise))
                    });
                    let premise = premise?;
                    bytes.push(value);
                    byte_equalities.push(premise);
                }
                let evidence = Self {
                    memory,
                    object,
                    profile,
                    word: word.clone(),
                    bytes: bytes.try_into().ok()?,
                    byte_equalities: byte_equalities.try_into().ok()?,
                };
                let checked = evidence.checks_equality(word, &result.into(), assumptions);
                if !checked {
                    return None;
                }
                for premise in &evidence.byte_equalities {
                    crate::kernel::record_implicit_reasoning_provenance(assumptions, premise);
                }
                Some(evidence)
            })
    }

    pub(in crate::kernel) fn checks_equality(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        assumptions: &PureFactContext,
    ) -> bool {
        let packed = pack_bytes(self.bytes.map(|byte| u32::from(byte).into()));
        if !((left == &self.word && right == &packed) || (right == &self.word && left == &packed))
            || Self::word_origin(&self.word) != Some((self.memory.clone(), self.object.clone()))
            || self.memory.declared_uint32_representation(&self.object) != Some(self.profile)
            || !initialized_span(&self.memory, &self.object, 4)
        {
            return false;
        }
        let observation_word = canonical_term(&self.word);
        self.byte_equalities
            .iter()
            .enumerate()
            .all(|(byte, premise)| {
                let observation = project_byte(observation_word.clone(), byte as u32);
                let value = Bitvector32Term::Constant(u32::from(self.bytes[byte]));
                assumptions.contains_assumed_exact(premise)
                    && matches!(premise,
                        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true)
                            if (canonical_term(left) == observation && right.as_ref() == &value)
                                || (canonical_term(right) == observation && left.as_ref() == &value))
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn declared(name: &str) -> (CMemory, Pointer) {
        let object = Pointer {
            block: format!("local:uint32-representation-{name}").into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = CMemory::new().with_declared_scalar_block_in_target(
            object.block.clone(),
            4,
            CType::UInt32,
            Some(ByteOrder::Little),
        );
        (memory, object)
    }

    fn byte_facts(word: &Bitvector32Term) -> PureFactContext {
        [120u32, 86, 52, 18].into_iter().enumerate().fold(
            PureFactContext::new(),
            |context, (byte, value)| {
                context.assume_proposition(Proposition::ConditionIs(
                    ConditionTerm::equal(project_byte(word.clone(), byte as u32), value.into()),
                    true,
                ))
            },
        )
    }

    fn symbolic_word(memory: &CMemory, object: &Pointer) -> Bitvector32Term {
        let Some(CValue::UInt32(word)) = observe_value(memory, object, CType::UInt32, true) else {
            panic!("an initialized declaration has a word observation");
        };
        word
    }

    #[test]
    fn uint32_representation_program_and_logical_reads_share_the_selected_snapshot() {
        let (memory, object) = declared("shared");
        let memory = memory.store(object.clone(), CValue::UInt32(0x12345678u32.into()));
        for (byte, expected) in [120u32, 86, 52, 18].into_iter().enumerate() {
            let pointer = object.offset_by_bytes(byte as u32);
            let logical = super::super::memory_loads::evaluate_logical_memory_load_paths(
                &memory,
                pointer.clone(),
                CType::UInt8,
                ExecutionFacts::new(),
                Vec::new(),
                &PureFactContext::new(),
            );
            let program = super::super::memory_loads::evaluate_c_memory_load_paths(
                &memory,
                pointer,
                CType::UInt8,
                ExecutionFacts::new(),
                Vec::new(),
                &PureFactContext::new(),
                false,
                false,
                None,
                None,
            );
            assert!(
                matches!(&logical[0].outcome, CExpressionOutcome::Value(CValue::UInt8(value))
                if value.as_const() == Some(expected))
            );
            assert!(
                matches!(&program[0].outcome, CExpressionOutcome::Value(CValue::UInt8(value))
                if value.as_const() == Some(expected))
            );
        }
        let word = symbolic_word(&memory, &object);
        for byte in 0..4 {
            assert_eq!(
                observe_value(&memory, &object.offset_by_bytes(byte), CType::UInt8, true),
                Some(CValue::UInt8(project_byte(word.clone(), byte)))
            );
            let logical = super::super::memory_loads::evaluate_logical_memory_load_paths(
                &memory,
                object.offset_by_bytes(byte),
                CType::UInt8,
                ExecutionFacts::new(),
                Vec::new(),
                &PureFactContext::new().keep_spec_loads_symbolic(),
            );
            assert!(logical[0].facts.is_empty());
            assert_eq!(
                logical[0].outcome,
                CExpressionOutcome::Value(CValue::UInt8(project_byte(word.clone(), byte)),)
            );
        }
        let (mut bytes, bytes_object) = declared("byte-stores");
        for byte in [2u32, 0, 3, 1] {
            let value = (0x12345678u32 >> (8 * byte)) & 255;
            bytes = bytes.store(
                bytes_object.offset_by_bytes(byte),
                CValue::UInt8(value.into()),
            );
        }
        assert_eq!(
            observe_value(&bytes, &bytes_object, CType::UInt32, false),
            Some(CValue::UInt32(0x12345678u32.into()))
        );
        assert!(!bytes.has_initialized_bytes_at(&bytes_object, 4));
    }

    #[test]
    fn uint32_packing_retains_named_load_byte_premises_and_rejects_an_overwrite() {
        let _session = crate::kernel::VerificationSession::enter();
        let (memory, object) = declared("named-byte-premises");
        let memory = memory.with_initialized_object(&object, 4);
        let word = symbolic_word(&memory, &object);
        let Bitvector32Term::Variable(variable) = &word else {
            panic!("symbolic word");
        };
        let (snapshot, address) = registered_load_for_variable(variable).unwrap();
        let named = Bitvector32Term::MemoryLoad(snapshot, Box::new(address), LoadKind::Bits32);
        assert_eq!(canonical_term(&named), word);
        let assumptions = byte_facts(&named);
        let result = Bitvector32Term::Constant(0x12345678);
        let evidence = UInt32PackingEvidence::for_equality(&word, &result, &assumptions)
            .expect("exact named observations establish all four bytes");
        assert!(evidence.checks_equality(&word, &result, &assumptions));
        for premise in &evidence.byte_equalities {
            let withdrawn = assumptions.without_exact_fact(premise);
            assert!(!evidence.checks_equality(&word, &result, &withdrawn));
            assert!(UInt32PackingEvidence::for_equality(&word, &result, &withdrawn).is_none());
        }
        let changed = memory.store(object.offset_by_bytes(2), CValue::UInt8(0u32.into()));
        let changed_word = symbolic_word(&changed, &object);
        assert!(
            UInt32PackingEvidence::for_equality(&changed_word, &result, &assumptions).is_none()
        );
    }

    #[test]
    fn uint32_representation_packing_retains_four_exact_initialized_byte_facts() {
        let (memory, object) = declared("packing");
        assert!(observe_value(&memory, &object, CType::UInt32, true).is_none());
        let memory = memory.with_initialized_object(&object, 4);
        let word = symbolic_word(&memory, &object);
        let result = Bitvector32Term::Constant(0x12345678);
        let assumptions = byte_facts(&word);
        let evidence = UInt32PackingEvidence::for_equality(&word, &result, &assumptions).unwrap();
        assert!(evidence.checks_equality(&word, &result, &assumptions));
        assert!(matches!(
            assumptions
                .proves_atomic_for_derivation_with_id(
                    &Proposition::ConditionIs(
                        ConditionTerm::equal(word.clone(), result.clone()),
                        true
                    ),
                    true,
                )
                .0,
            Some(AtomicPropositionDerivationEvidence::UInt32Representation(_))
        ));
        for premise in &evidence.byte_equalities {
            let missing = assumptions.without_exact_fact(premise);
            assert!(!evidence.checks_equality(&word, &result, &missing));
            assert!(UInt32PackingEvidence::for_equality(&word, &result, &missing).is_none());
        }
        assert!(!evidence.checks_equality(&word, &0u32.into(), &assumptions));
        let changed = memory
            .clone()
            .store(object.offset_by_bytes(2), CValue::UInt8(0u32.into()));
        let changed_word = symbolic_word(&changed, &object);
        assert!(!evidence.checks_equality(&changed_word, &result, &assumptions));
        assert!(
            UInt32PackingEvidence::for_equality(&changed_word, &result, &assumptions).is_none()
        );
        let changed_read = Bitvector32Term::MemoryLoad(
            intern_c_memory_ref(&changed),
            Box::new(object.clone()),
            LoadKind::Bits32,
        );
        assert!(
            UInt32PackingEvidence::for_equality(&changed_read, &result, &assumptions).is_none()
        );
        assert_eq!(memory.known_value(&object), None);
        assert!(memory.has_initialized_bytes_at(&object, 4));
    }

    #[test]
    fn uint32_representation_derivation_checks_only_its_four_selected_byte_premises() {
        let (memory, object) = declared("retained-packing");
        let memory = memory.with_initialized_object(&object, 4);
        let word = symbolic_word(&memory, &object);
        let goal_word = Bitvector32Term::MemoryLoad(
            intern_c_memory_ref(&memory),
            Box::new(object.clone()),
            LoadKind::Bits32,
        );
        assert_eq!(canonical_term(&goal_word), word);
        let result = Bitvector32Term::Constant(0x12345678);
        let goal = Proposition::ConditionIs(
            ConditionTerm::equal(goal_word.clone(), result.clone()),
            true,
        );
        let unrelated = Proposition::ConditionIs(
            ConditionTerm::equal(Bitvector32Term::Variable(Variable(9_746_001)), 17u32.into()),
            true,
        );
        let ambient = byte_facts(&word).assume_proposition(unrelated.clone());
        let ((evidence, premises_id), selected) =
            crate::kernel::collect_reasoning_provenance(|| {
                crate::kernel::capture_implicit_reasoning_provenance(|| {
                    ambient.proves_atomic_for_derivation_with_id(&goal, true)
                })
            });
        let evidence = evidence.expect("four exact byte values determine the selected word");
        let AtomicPropositionDerivationEvidence::UInt32Representation(packing) = &evidence else {
            panic!("the derivation must retain the packing certificate");
        };
        assert_eq!(selected.len(), 4);
        assert!(!selected.contains(&unrelated));
        for premise in &packing.byte_equalities {
            assert!(selected.contains(premise));
        }
        let selected = selected
            .into_iter()
            .fold(PureFactContext::new(), PureFactContext::assume_proposition);
        let derivation = PropositionDerivation {
            conclusion: goal,
            rule: PropositionDerivationRule::ContextualAtomic {
                premises: RetainedPremises::from_context(&selected),
                premises_id,
                for_simp: true,
                evidence,
            },
        };
        assert!(derivation.check(&ambient));
        assert!(derivation.check(&selected));
        for premise in derivation.context_premises() {
            assert!(!derivation.check(&selected.without_exact_fact(&premise)));
        }

        let change_packing = |mut proof: PropositionDerivation,
                              change: fn(&mut UInt32PackingEvidence)| {
            let PropositionDerivationRule::ContextualAtomic {
                evidence: AtomicPropositionDerivationEvidence::UInt32Representation(packing),
                ..
            } = &mut proof.rule
            else {
                panic!("the original certificate is typed packing evidence");
            };
            change(packing);
            proof
        };
        let mut wrong_byte = change_packing(derivation.clone(), |packing| {
            packing.bytes[0] = 121;
        });
        // Retarget the result too: the old byte premise still cannot justify
        // the new packed value, even though it matches the mutated bytes.
        wrong_byte.conclusion = Proposition::ConditionIs(
            ConditionTerm::equal(goal_word.clone(), 0x12345679u32.into()),
            true,
        );
        assert!(!wrong_byte.check(&selected));
        let wrong_premise = change_packing(derivation.clone(), |packing| {
            packing.byte_equalities[1] = packing.byte_equalities[0].clone();
        });
        assert!(!wrong_premise.check(&selected));
        let wrong_root = change_packing(derivation.clone(), |packing| {
            packing.object = packing.object.offset_by_bytes(1);
        });
        assert!(!wrong_root.check(&selected));
        let wrong_snapshot = change_packing(derivation.clone(), |packing| {
            let changed = packing.memory.memory().clone().store(
                packing.object.offset_by_bytes(2),
                CValue::UInt8(0u32.into()),
            );
            packing.memory = intern_c_memory(changed);
        });
        assert!(!wrong_snapshot.check(&selected));
        assert!(derivation.check(&selected));
        assert_eq!(memory.known_value(&object), None);
    }

    #[test]
    fn uint32_representation_refuses_partial_adjacent_unsupported_and_wide_observations() {
        let (memory, object) = declared("refusals");
        let partial = memory.clone().with_initialized_object(&object, 3);
        assert!(observe_value(&partial, &object, CType::UInt32, true).is_none());
        assert!(observe_value(&partial, &object.offset_by_bytes(2), CType::UInt8, true).is_some());
        assert!(!partial.has_initialized_bytes_at(&object, 4));
        let complete = memory.with_initialized_object(&object, 4);
        assert!(observe_value(&complete, &object.offset_by_bytes(4), CType::UInt8, true).is_none());
        assert!(observe_value(&complete, &object, CType::Int32, true).is_none());
        for (c_type, order) in [
            (CType::UInt32, None),
            (CType::UInt32, Some(ByteOrder::Big)),
            (CType::Int32, Some(ByteOrder::Little)),
        ] {
            let unsupported = CMemory::new()
                .with_declared_scalar_block_in_target(object.block.clone(), 4, c_type, order)
                .with_initialized_object(&object, 4);
            assert!(observe_value(&unsupported, &object, CType::UInt32, true).is_none());
        }
        let byte_array = CMemory::new()
            .with_declared_array_block(object.block.clone(), CType::UInt8, 4)
            .unwrap()
            .with_initialized_object(&object, 4);
        assert!(observe_value(&byte_array, &object, CType::UInt32, true).is_none());
        let word = symbolic_word(&complete, &object);
        let assumptions = byte_facts(&word);
        let raw = Bitvector32Term::MemoryLoad(
            intern_c_memory_ref(&complete),
            Box::new(object.clone()),
            LoadKind::Bits32,
        );
        super::super::memory_loads::symbolic_storage_cell_value(
            &complete,
            &object,
            CType::Int64,
            true,
        )
        .unwrap();
        assert!(UInt32PackingEvidence::word_origin(&raw).is_none());
        let wrong_kind = Bitvector32Term::MemoryLoad(
            intern_c_memory_ref(&complete),
            Box::new(object),
            LoadKind::UInt8,
        );
        assert!(
            UInt32PackingEvidence::for_equality(&wrong_kind, &0x12345678u32.into(), &assumptions)
                .is_none()
        );
    }

    #[test]
    fn uint32_representation_packing_work_ignores_unrelated_equalities_and_cells() {
        let mut measured = Vec::new();
        for count in [16u32, 128, 1024] {
            let (mut memory, object) = declared(&format!("scaling-{count}"));
            memory = memory.with_initialized_object(&object, 4);
            for index in 0..count {
                memory = memory.store(
                    Pointer {
                        block: format!("uint32-unrelated-{index}").into(),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                    CValue::UInt32(index.into()),
                );
            }
            let word = symbolic_word(&memory, &object);
            let mut assumptions = byte_facts(&word);
            for index in 0..count {
                assumptions = assumptions.assume_proposition(Proposition::ConditionIs(
                    ConditionTerm::equal(
                        Bitvector32Term::Variable(Variable(9_745_000 + u64::from(index))),
                        index.into(),
                    ),
                    true,
                ));
            }
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let evidence =
                    UInt32PackingEvidence::for_equality(&word, &0x12345678u32.into(), &assumptions)
                        .unwrap();
                assert!(evidence.checks_equality(&word, &0x12345678u32.into(), &assumptions));
            });
            measured.push(work);
        }
        assert!(
            measured.iter().all(|work| *work <= measured[0] + 8),
            "{measured:?}"
        );
    }
}
