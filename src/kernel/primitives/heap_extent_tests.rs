use super::*;

fn hash_of(value: &impl std::hash::Hash) -> u64 {
    use std::hash::Hasher;
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

/// Memory state hashes name symbolic loads, so tagging every existing (32-bit)
/// extent must not change them: an `Int32` extent hashes and prints as its
/// byte term. The kind still separates the two extents of one term.
#[test]
fn a_32_bit_extent_hashes_and_prints_as_its_bytes() {
    let _session = crate::kernel::VerificationSession::enter();
    let bytes = MachineTerm::Variable(Variable(7));
    let narrow = HeapExtent::int32(bytes.clone());
    let wide = HeapExtent::new(bytes.clone(), HeapExtentKind::UInt64);
    assert_eq!(hash_of(&narrow), hash_of(&bytes));
    assert_eq!(format!("{narrow:?}"), format!("{bytes:?}"));
    assert_ne!(narrow, wide);
    assert_ne!(hash_of(&narrow), hash_of(&wide));
}

/// The `allocation` token, its owned range, and its coverage carry the
/// extent's kind, and reading the token back recovers it.
#[test]
fn allocation_tokens_and_ranges_carry_the_extent_kind() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer {
        block: PointerBlock::Heap(3),
        offset: PointerOffsetTerm::Constant(0),
    };
    for (extent, value_is_wide, range_kind) in [
        (HeapExtent::int32(16), false, RangeIndexKind::Int32),
        (
            HeapExtent::new(MachineTerm::uint64_constant(16), HeapExtentKind::UInt64),
            true,
            RangeIndexKind::UInt64,
        ),
    ] {
        let token = ResourceFact::own_heap_allocation(base.clone(), &extent);
        let (read_base, read_extent) = token.allocation_extent().expect("an allocation token");
        assert_eq!(read_base.pointer(), &base);
        assert_eq!(read_extent, extent);
        assert_eq!(
            token.allocation().map(|(_, bytes)| bytes),
            Some(extent.bytes())
        );
        assert_eq!(
            matches!(extent.token_value(), ProgramValue::UInt64(_)),
            value_is_wide
        );
        assert_eq!(extent.byte_range(base.clone()).kind(), range_kind);
    }
}

/// A 64-bit extent spells its element count at `uint64`: `n` of `n * w`
/// and a divisible constant; a 32-bit extent keeps the 32-bit reading, and
/// neither reads the other's format.
#[test]
fn a_64_bit_extent_counts_its_elements_at_uint64() {
    let _session = crate::kernel::VerificationSession::enter();
    let n = MachineTerm::Variable(Variable(7));
    let wide = |bytes| HeapExtent::new(bytes, HeapExtentKind::UInt64);
    let product = wide(MachineTerm::uint64_multiply(
        n.clone(),
        MachineTerm::uint64_constant(4),
    ));
    assert_eq!(product.element_count(4), Some(n.clone()));
    assert_eq!(product.element_count(8), None);
    assert_eq!(product.element_count(1), Some(product.bytes().clone()));
    let constant = wide(MachineTerm::uint64_constant(1 << 35));
    assert_eq!(
        constant.element_count(8),
        Some(MachineTerm::uint64_constant(1 << 32))
    );
    assert_eq!(
        wide(MachineTerm::uint64_constant((1 << 35) + 2)).element_count(4),
        None
    );
    let narrow = HeapExtent::int32(MachineTerm::multiply(n.clone(), MachineTerm::constant(4)));
    assert_eq!(narrow.element_count(4), Some(n.clone()));
    assert_eq!(
        HeapExtent::int32(product.bytes().clone()).element_count(4),
        None
    );
}
