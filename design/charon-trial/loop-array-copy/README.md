# Loop-local scalar-array copies

The frozen `quad.rs` is the original reduced reproduction of a missing backing
failure. Each iteration of a stored four-byte chunk loop returns a record,
copies its lane array into a fresh local array, and reads its second element.
The sidecar proves all four copied values at a symbolic loop head and termination
over sixteen bytes without naming local array temporaries in loop resources.
An empty-input contract exercises the same unchanged source without an iteration.

Native array `StorageLive` events allocate compact checked automatic storage at
their actual execution point. Plain record storage starts also recreate backing,
so their array fields remain readable by state copies. Array locals without a
storage-start event retain entry backing. Re-entering a declaration retires its
old object, checks live loans, and mints a distinct object identity. This does not
relax array-copy read/write authority or record move/drop checks. Storage end
continues to use the existing conservative lowering; this increment does not
claim general Rust reference-lifetime export.

Normal tests reject missing storage starts, omitted initialization, a restart
that loses initialized bytes, incorrect extents, false copied values, and
missing input views. Layout/node counts stay independent of array extent at
4, 1,024, and 1,000,000 elements. Nightly checks expand and reverify the checked
certificate and run profiling. The original Adler trial exercises the related
copy into its array-bearing vector temporary; full Adler induction is separate.
