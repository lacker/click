use super::*;
use crate::kernel::functions::transfer_representation_copy_cells;

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
