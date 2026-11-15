// Scaling tests of `src/kernel/primitives/cell_store.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn retained_run_reads_refresh_load_origins_without_scanning_the_run() {
    let mut samples = Vec::new();
    for count in [16, 64, 65, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = source(99);
        let base = constant(&PointerBlock::from("cell-store-source-99"), 0);
        let run = run(base.clone(), 4, count, &source);
        let first = run.value(0);
        let ProgramValue::Int32(ref read) = first else {
            panic!("a seeded scalar names its source load");
        };
        let observation = || {
            crate::kernel::eval::scalar_read_observation(crate::kernel::MachineOperandView::Legacy(
                read,
            ))
            .and_then(|read| read.origin.map(|origin| (origin, read.pointer)))
        };
        assert!(matches!(read, crate::kernel::MachineTerm::MemoryLoad(..)));
        assert!(observation().is_some());
        crate::kernel::eval::begin_load_origin_epoch();
        assert!(observation().is_none());
        assert_eq!(run.value(0), first);
        assert_eq!(
            observation(),
            Some((source, base)),
            "a retained {count}-cell run must observe the load in this epoch"
        );
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..16 {
                assert_eq!(run.value(0), first);
            }
        });
        samples.push((count, work));
    }
    assert!(
        samples.iter().all(|(_, work)| *work == samples[0].1),
        "repeated seeded reads must use the epoch cache without scanning the run: {samples:?}"
    );
}

#[test]
fn selected_cell_metadata_refuses_growing_cover_buckets_without_scanning() {
    let mut samples = Vec::new();
    for size in [4u32, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = source(99);
        let block = PointerBlock::Concrete("metadata-cover".into());
        let stride = size * 4;
        let target = constant(&block, i64::from(stride));
        let mut single = CellStore::new();
        single.add_run(run(constant(&block, 0), stride, 2, &source));
        let mut ambiguous = single.clone();
        for index in 1..size {
            // Disjoint strided slots, but all spans cover the target. A live
            // slot search would have to inspect the whole candidate bucket.
            ambiguous.add_run(run(
                constant(&block, i64::from(index * 4)),
                stride,
                2,
                &source,
            ));
            single.add_run(run(
                constant(&PointerBlock::Concrete(format!("other-{index}")), 0),
                4,
                1,
                &source,
            ));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(single.value_type_at(&target), Some(ProgramType::Int32));
            assert_eq!(ambiguous.value_type_at(&target), None);
            assert_eq!(single.value_type_at(&constant(&block, 1)), None);
        });
        samples.push(work);
    }
    assert!(
        samples[0] > 0 && samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}
