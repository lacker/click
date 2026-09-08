use super::*;

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
        assert_ne!(signature, 0);
        if arity > 2 {
            assert!(seen.insert(signature));
        }
    }
    assert_eq!(
        CType::function_pointer_signature(CType::Void, &[CType::Int32; 14]),
        0
    );
}
