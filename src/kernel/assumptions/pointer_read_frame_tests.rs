use super::*;

fn read(context: &PureFactContext, memory: &CMemory, address: &Pointer) -> Pointer {
    let memory = crate::kernel::intern_c_memory(memory.clone());
    let variable = crate::kernel::load_variable_for_cell_with_origin(
        &memory,
        address,
        LoadKind::Pointer,
        crate::kernel::C_POINTER_BYTE_WIDTH,
        &memory,
    );
    let value = Pointer::loaded(
        PointerBlock::ExternalArgument,
        Bitvector32Term::Variable(variable),
        4,
    );
    context.register_pointer_read(&value, &memory, address);
    value
}

fn range(base: Pointer, elements: u32, stride: u32) -> CResource {
    CResource::Memory(CMemoryRange::new_with_element_width(
        base,
        0u32.into(),
        elements.into(),
        stride,
    ))
}

fn fixture() -> (
    PureFactContext,
    CMemory,
    Pointer,
    Pointer,
    Pointer,
    Proposition,
) {
    let before = CMemory::new();
    let owner = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let address = owner.offset_by_bytes(8);
    let source = read(&PureFactContext::new(), &before, &address);
    let write = source.offset_by_bytes(4);
    let separation = Proposition::CResourceSeparate {
        left: Box::new(range(owner, 4, 4)),
        right: Box::new(range(source.clone(), 4, 4)),
    };
    let context = PureFactContext::new().assume_proposition(separation.clone());
    let after = before
        .with_block("local:frame-unrelated", 4)
        .store(write.clone(), int32(7));
    (context, after, address, source, write, separation)
}

#[test]
fn selected_pointer_read_frame_retains_full_span_and_current_authority() {
    let _session = crate::kernel::VerificationSession::enter();
    let (context, after, address, source, _, separation) = fixture();
    let current = read(&context, &after, &address);
    assert_ne!(source, current);
    // The supported frame remains outside the unconditional graph closure.
    assert!(!context.equality_graph.are_equal(&source, &current));
    let capture = crate::kernel::memory_provenance::CheckedLoadEqualityCapture::start();
    assert!(context.pointers_known_equal(&source, &current));
    let proofs = capture.finish();
    assert!(!proofs.is_empty());
    assert!(proofs.iter().all(|proof| proof.checks(&context)));
    assert!(
        crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
            &source, &current, &context,
        )
    );
    let withdrawn = context.without_exact_fact(&separation);
    assert!(!withdrawn.pointers_known_equal(&source, &current));
    assert!(proofs.iter().all(|proof| !proof.checks(&withdrawn)));
    assert!(
        !context
            .restricted_to_facts(&[], &[])
            .pointers_known_equal(&source, &current)
    );

    let wrong_cell = read(&context, &after, &address.offset_by_bytes(8));
    assert!(!context.pointers_known_equal(&source, &wrong_cell));
    let overlap = after.store(address.offset_by_bytes(4), int32(9));
    let overlapping_read = read(&context, &overlap, &address);
    assert!(!context.pointers_known_equal(&source, &overlapping_read));
    assert!(!context.pointers_known_equal(&source.offset_by_bytes(4), &current));
}

#[test]
fn selected_pointer_read_frame_work_ignores_unrelated_ranges_and_withdrawal() {
    let _session = crate::kernel::VerificationSession::enter();
    let (root, after, address, source, _, _) = fixture();
    let mut samples = Vec::new();
    for size in [16, 128, 1024] {
        let mut context = root.clone();
        let mut last = None;
        for index in 0..size {
            let pointer = |side: &str| Pointer {
                block: format!("frame:unrelated-{side}-{index}").into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            let fact = Proposition::CResourceSeparate {
                left: Box::new(range(pointer("left"), 1, 8)),
                right: Box::new(range(pointer("right"), 1, 8)),
            };
            context = context.assume_proposition(fact.clone());
            last = Some(fact);
        }
        let (current, producer_work) =
            crate::instrumentation::measure_deterministic_work(|| read(&context, &after, &address));
        let ((weakened, equal), query_work) =
            crate::instrumentation::measure_deterministic_work(|| {
                let weakened = context.without_exact_fact(last.as_ref().unwrap());
                let equal = weakened.pointers_known_equal(&source, &current);
                (weakened, equal)
            });
        assert!(equal);
        assert!(weakened.pointers_known_equal(&source, &current));
        samples.push((producer_work, query_work));
    }
    assert!(
        samples
            .iter()
            .all(|(production, query)| *production <= samples[0].0 + 64
                && *query <= samples[0].1 + 64),
        "selected frame work changed with unrelated ranges: {samples:?}"
    );
}
