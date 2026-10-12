use super::*;

/// Reconstruct one initialized declared uint32 observation from its four
/// exact byte values. The retained load supplies the declaration, target and
/// initialization evidence; the theorem still requires all four byte facts.
pub fn prove_declared_uint32_from_bytes(word: Bitvector32Term, value: u32) -> Option<Theorem> {
    let observation = super::super::eval::canonical_term(&word);
    let premises = (0..4)
        .map(|byte| {
            Proposition::ConditionIs(
                ConditionTerm::equal(
                    super::super::eval::uint32_representation::project_byte(
                        observation.clone(),
                        byte,
                    ),
                    ((value >> (8 * byte)) & 255).into(),
                ),
                true,
            )
        })
        .collect::<Vec<_>>();
    let assumptions = premises
        .iter()
        .cloned()
        .fold(PureFactContext::new(), PureFactContext::assume_proposition);
    let evidence = UInt32PackingEvidence::for_equality(&word, &value.into(), &assumptions)?;
    if !evidence.checks_equality(&word, &value.into(), &assumptions) {
        return None;
    }
    let guard = premises
        .into_iter()
        .reduce(|left, right| Proposition::And(Box::new(left), Box::new(right)))?;
    Some(Theorem::new(Proposition::Implies(
        Box::new(guard),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(word, value.into()),
            true,
        )),
    )))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn observed(memory: &CMemory, object: &Pointer, bytes: u32) -> Bitvector32Term {
        let snapshot = intern_c_memory_ref(memory);
        super::super::super::eval::load_variable_for_exact_cell(
            &snapshot,
            object,
            LoadKind::Bits32,
            bytes,
        );
        Bitvector32Term::MemoryLoad(snapshot, Box::new(object.clone()), LoadKind::Bits32)
    }

    #[test]
    fn declared_uint32_from_bytes_requires_the_selected_initialized_profile_and_exact_width() {
        let _session = crate::kernel::VerificationSession::enter();
        let object = Pointer {
            block: "local:guarded-uint32-theorem".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let declared = CMemory::new().with_declared_scalar_block_in_target(
            object.block.clone(),
            4,
            CType::UInt32,
            Some(ByteOrder::Little),
        );
        for count in [0, 3] {
            let partial = declared.clone().with_initialized_object(&object, count);
            assert!(
                prove_declared_uint32_from_bytes(observed(&partial, &object, 4), 0x12345678)
                    .is_none()
            );
        }
        let complete = declared.with_initialized_object(&object, 4);
        let theorem =
            prove_declared_uint32_from_bytes(observed(&complete, &object, 4), 0x12345678).unwrap();
        let Proposition::Implies(guard, _) = theorem.proposition() else {
            panic!("packing must cite byte values");
        };
        let mut selected = Vec::new();
        let mut pending = vec![guard.as_ref()];
        while let Some(proposition) = pending.pop() {
            if let Proposition::And(left, right) = proposition {
                pending.extend([left.as_ref(), right.as_ref()]);
            } else {
                selected.push(proposition);
            }
        }
        assert_eq!(selected.len(), 4);
        assert!(selected.iter().all(|premise| matches!(
            premise,
            Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(..), true)
        )));
        for order in [None, Some(ByteOrder::Big)] {
            let unsupported = CMemory::new()
                .with_declared_scalar_block_in_target(object.block.clone(), 4, CType::UInt32, order)
                .with_initialized_object(&object, 4);
            assert!(
                prove_declared_uint32_from_bytes(observed(&unsupported, &object, 4), 0x12345678)
                    .is_none()
            );
        }
        let bytes = CMemory::new()
            .with_declared_array_block(object.block.clone(), CType::UInt8, 4)
            .unwrap()
            .with_initialized_object(&object, 4);
        assert!(
            prove_declared_uint32_from_bytes(observed(&bytes, &object, 4), 0x12345678).is_none()
        );
        assert!(
            prove_declared_uint32_from_bytes(observed(&complete, &object, 8), 0x12345678).is_none()
        );
        assert_eq!(complete.known_value(&object), None);
    }
}
