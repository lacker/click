use super::*;
use crate::kernel::functions::{
    representation_copy_cell_moves, transfer_representation_copy_cells,
};

fn heap_pointer(block: &str) -> Pointer {
    Pointer {
        block: PointerBlock::from(block),
        offset: PointerOffsetTerm::Constant(0),
    }
}

fn copy_arguments(destination: &Pointer, source: &Pointer, bytes: u32) -> Vec<CValue> {
    vec![
        CValue::typed_pointer(destination.clone(), CType::UInt8Pointer),
        CValue::typed_pointer(source.clone(), CType::UInt8Pointer),
        CValue::Int32(Bitvector32Term::Constant(bytes)),
    ]
}

fn effect() -> RepresentationCopyEffect {
    RepresentationCopyEffect {
        destination_argument: 0,
        source_argument: 1,
        bytes_argument: 2,
    }
}

#[test]
fn representation_copy_transfers_a_fully_covered_cell() {
    let source = heap_pointer("copy-source");
    let destination = heap_pointer("copy-destination");
    let entry = CMemory::new().store(source.clone(), CValue::UInt32(Bitvector32Term::Constant(7)));

    let result = transfer_representation_copy_cells(
        &entry,
        &copy_arguments(&destination, &source, 4),
        CMemory::new(),
        effect(),
    );

    assert_eq!(
        result.known_value(&destination),
        Some(CValue::UInt32(Bitvector32Term::Constant(7)))
    );
}

#[test]
fn representation_copy_leaves_a_split_cell_unestablished() {
    let source = heap_pointer("split-source");
    let destination = heap_pointer("split-destination");
    let entry = CMemory::new().store(source.clone(), CValue::UInt32(Bitvector32Term::Constant(7)));

    let result = transfer_representation_copy_cells(
        &entry,
        &copy_arguments(&destination, &source, 2),
        CMemory::new(),
        effect(),
    );

    assert_eq!(result.known_value(&destination), None);
}

#[test]
fn representation_copy_leaves_an_untyped_source_unestablished() {
    let source = heap_pointer("untyped-source");
    let destination = heap_pointer("untyped-destination");

    let result = transfer_representation_copy_cells(
        &CMemory::new(),
        &copy_arguments(&destination, &source, 4),
        CMemory::new(),
        effect(),
    );

    assert_eq!(result.known_value(&destination), None);
}

fn cell(block: &str, index: u32) -> Pointer {
    Pointer {
        block: PointerBlock::from(block),
        offset: PointerOffsetTerm::Constant(4 * i64::from(index)),
    }
}

fn cell_value(index: u32) -> CValue {
    CValue::UInt32(Bitvector32Term::Constant(index))
}

fn source_with_cells(memory: CMemory, block: &str, cells: u32) -> CMemory {
    (0..cells).fold(memory, |memory, index| {
        memory.store(cell(block, index), cell_value(index))
    })
}

/// Measures the cell lookup of one transfer of `cells` four-byte cells and
/// checks that the complete transfer plants every copied cell.
///
/// The lookup is the transfer's own work. Planting each result is an ordinary
/// `CMemory::store`, whose cost belongs to the store primitive and has its
/// own regressions in `memory_scaling_tests`; the whole transfer's work is
/// reported in the failure messages.
fn copy_lookup_work(
    entry: &CMemory,
    memory: &CMemory,
    source: &str,
    destination: &str,
    cells: u32,
) -> (usize, usize) {
    let arguments = copy_arguments(&heap_pointer(destination), &heap_pointer(source), 4 * cells);
    let (moves, lookup_work) = crate::instrumentation::measure_deterministic_work(|| {
        representation_copy_cell_moves(entry, &arguments, effect())
    });
    assert_eq!(moves.len(), cells as usize);
    let (result, transfer_work) = crate::instrumentation::measure_deterministic_work(|| {
        transfer_representation_copy_cells(entry, &arguments, memory.clone(), effect())
    });
    for index in 0..cells {
        assert_eq!(
            result.known_value(&cell(destination, index)),
            Some(cell_value(index))
        );
    }
    (lookup_work, transfer_work)
}

#[test]
fn representation_copy_lookup_work_is_linear_in_the_copied_extent() {
    let mut lookups = Vec::new();
    let mut transfers = Vec::new();
    for cells in [4_u32, 8, 16, 32, 64] {
        let entry = source_with_cells(CMemory::new(), "extent-source", cells);
        let (lookup, transfer) = copy_lookup_work(
            &entry,
            &CMemory::new(),
            "extent-source",
            "extent-destination",
            cells,
        );
        lookups.push(lookup);
        transfers.push(transfer);
        // One unit for the range query, one per copied cell it visits.
        assert_eq!(
            lookup,
            1 + cells as usize,
            "copied-extent lookup work: {lookups:?}; whole transfer: {transfers:?}"
        );
    }
    assert!(
        lookups.windows(2).all(|pair| pair[1] <= 2 * pair[0]),
        "copied-extent lookup work grew faster than the extent: {lookups:?}"
    );
}

#[test]
fn fixed_representation_copy_lookup_work_is_independent_of_unrelated_memory() {
    let mut lookups = Vec::new();
    let mut transfers = Vec::new();
    for unrelated in [8_u32, 32, 128, 512] {
        let mut memory = source_with_cells(CMemory::new(), "fixed-source", 4);
        for index in 0..unrelated {
            memory = memory.store(cell(&format!("unrelated-{index}"), 0), cell_value(index));
            // Source-block cells past the copied range are not visited either.
            memory = memory.store(cell("fixed-source", 4 + index), cell_value(index));
        }
        let (lookup, transfer) =
            copy_lookup_work(&memory, &memory, "fixed-source", "fixed-destination", 4);
        lookups.push(lookup);
        transfers.push(transfer);
    }
    assert!(
        lookups.iter().all(|work| *work == 5),
        "fixed-copy lookup work grew with unrelated memory: {lookups:?}; whole transfer: {transfers:?}"
    );
    assert!(
        transfers.iter().all(|work| *work == transfers[0]),
        "fixed-copy transfer work grew with unrelated memory: {transfers:?}; lookups: {lookups:?}"
    );
}
