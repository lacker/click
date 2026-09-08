use super::*;

#[test]
fn callback_qualification_identity_is_exact_at_every_position_and_arity() {
    let mut seen = std::collections::BTreeSet::new();
    for arity in 0..=13 {
        // Enumerate every qualification combination, including the highest
        // supported arity: neither a high bit nor leading zero is lost.
        for mask in 0..(1usize << (arity + 1)) {
            let parameters = (0..arity)
                .map(|index| (CType::VoidPointer, mask & (1 << (index + 1)) != 0))
                .collect::<Vec<_>>();
            let key = CType::qualified_function_pointer_signature(
                CType::VoidPointer,
                mask & 1 != 0,
                &parameters,
            );
            assert_ne!(key, CallbackSignature::UNSPECIFIED);
            assert!(seen.insert(key), "collision at arity {arity}, mask {mask}");
        }
    }
    assert_eq!(
        CType::qualified_function_pointer_signature(
            CType::VoidPointer,
            true,
            &[(CType::VoidPointer, true); 14]
        ),
        CallbackSignature::UNSPECIFIED
    );
    assert_eq!(
        CType::qualified_function_pointer_signature(CType::Int32, true, &[]),
        CallbackSignature::UNSPECIFIED
    );
    assert_eq!(
        CType::qualified_function_pointer_signature(CType::Void, false, &[(CType::Int32, true)]),
        CallbackSignature::UNSPECIFIED
    );
    assert!(std::mem::size_of::<CType>() <= 16);
    assert!(std::mem::size_of::<crate::languages::c::syntax::C0Type>() <= 16);
}

#[test]
fn callback_signature_codes_cannot_overlap_adjacent_types() {
    assert_ne!(
        CType::function_pointer_signature(CType::UInt64Pointer, &[CType::UInt8]),
        CType::function_pointer_signature(CType::Void, &[CType::UInt32]),
    );
    let types = [
        CType::Void,
        CType::Int32,
        CType::UInt8,
        CType::UInt32,
        CType::Int32Pointer,
        CType::UInt8Pointer,
        CType::Int32PointerPointer,
        CType::UInt8PointerPointer,
        CType::Int16,
        CType::UInt16,
        CType::Int64,
        CType::UInt64,
        CType::Int16Pointer,
        CType::UInt16Pointer,
        CType::UInt32Pointer,
        CType::Int64Pointer,
        CType::UInt64Pointer,
        CType::Float32,
        CType::Float64,
        CType::VoidPointer,
    ];
    let mut seen = std::collections::BTreeSet::new();
    for result in types {
        assert!(seen.insert(CType::function_pointer_signature(result, &[])));
        for first in types {
            assert!(seen.insert(CType::function_pointer_signature(result, &[first])));
            for second in types {
                assert!(seen.insert(CType::function_pointer_signature(result, &[first, second])));
            }
        }
    }
    for arity in 0..=13 {
        let parameters = vec![CType::VoidPointer; arity];
        let signature = CType::function_pointer_signature(CType::VoidPointer, &parameters);
        assert_ne!(signature, CallbackSignature::UNSPECIFIED);
        if arity > 2 {
            assert!(seen.insert(signature));
        }
    }
    assert_eq!(
        CType::function_pointer_signature(CType::Void, &[CType::Int32; 14]),
        CallbackSignature::UNSPECIFIED
    );
}
