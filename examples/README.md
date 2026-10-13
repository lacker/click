# Examples

This tree holds example projects that are larger than a single mdtest snippet.
Name directories after the domain and proof question, not after whether they are
"real" or "mini".

Each example project should contain ordinary `.c`, `.cpp`, or `.rs` files and one or
more `.click` sidecars. The `tests/examples.rs` integration test verifies every
sidecar against its source. Compiler-import examples also include an
`*.click.import.json` configuration; a project-local `prepare.py`, when
present, prepares portable local inputs such as a compilation database before
the gate refreshes the import and verifies it.

Most fixtures should stay small. Keep everything directly under `examples/`
unless there is a concrete reason to add hierarchy.

An example keeps its general proof and that proof's regressions. Per-case
increments are useful while a proof is developed, but once a general proof
subsumes an increment, delete the increment and point its mutation checks at
the general proof
([design/proof-reuse.md](../design/proof-reuse.md#r1-retire-superseded-increments-process)).

## Source provenance

Examples have three distinct provenance classes:

- **Synthetic** fixtures are C, C++, or Rust written for this repository to isolate a
  language or proof-model question. Their source should still remain fixed while a
  proof is repaired, but they are not evidence that Click accepts unchanged
  third-party source.
- **C transcriptions** are semantics-preserving translations of identified C
  into Click's supported C. They must include a `SOURCE.md` naming the
  upstream source and revision and recording every translation.
- **Unchanged existing-source** fixtures preserve identified upstream files
  byte-for-byte. They must include a `SOURCE.md` plus a checked source-integrity
  manifest so proof work cannot silently edit the imported C.

Most projects in this tree are synthetic. In particular, `jsonc-refcount/` is
deliberately **json-c-shaped**, not copied from json-c. The
`jsonc-existing-source/` project is the first unchanged-source fixture; its
SHA-256 manifest is checked by the examples gate before verifying its numeric
version and version-string bytes under the default user-space target.

Current projects:

- `clamp/` is the README quick start: a branchy `int` function proved in range
  with `by auto`.
- `basic-rust/` verifies scalar branches, reference reborrows, parent reuse, and
  disjoint struct fields through the pinned Rust compiler import.
- `rust-move-drop/` verifies a moved Rust guard that restores borrowed storage
  on normal and early return through a checked destructor contract.
- `rust-usize/` checks full-width checked arithmetic, casts, and computed slice indices.
- `rust-integer-conversions/` checks native unsigned `From`, checked halfword
  references/fields, and a fixed checksum-style accumulator update.
- `rust-unsigned/` checks Rust byte and word arithmetic, casts, and panic freedom.
- `rust-slices/` checks byte-slice lengths, indexed reads/writes, and slice calls.
- `rust-arrays/` checks fixed-array reference lengths, typed indexing, element
  reborrows, direct calls, and parent reuse.
- `rust-array-values/` checks local array construction, independent whole-array
  copies, assignment through references, and constructor evaluation order.
- `rust-array-slices/` checks fixed byte arrays coercing to shared/mutable slices,
  length metadata, slice reassignment, helper calls, and parent reuse.
- `rust-chunks-exact/` checks stored shared chunk iterators, cursor coverage,
  byte reads, and their fixed remainder without a generated progress count.
- `rust-field-borrow/` verifies nested Rust guards borrowing an owned field,
  with the inner destructor's write observed by the outer destructor.
- `basic-cpp/` verifies a small C++ reference mutation, an RAII guard that
  restores its referent on both normal and early return, and a modular caller
  that observes the captured result and restored memory, using Clang 19's
  compiler import.
- `multifile-registry/` combines shared counters, same-named private statics,
  persistent local arrays, repeated includes, and a data-only translation unit.
- `sequence-transform/` fixes small array copy, concatenation, reversal, and
  membership operations for the logical list model; its unchanged C and
  sidecar verify the implemented finite-literal precursor contracts.
- `modeled-binary-tree/` fixes a plain binary-tree implementation for the
  heap-derived in-order sequence model, membership, rotation-preservation, and
  structural-termination work required by MVR; its sidecar currently imports
  the C without claiming those proofs.
- `arena/` fixes the C implementation boundary for a first-fit allocator
  whose regions exercise user-defined suballocation and lifetime ownership.
  `arena_cells.click` verifies initialization, allocation anywhere, frees in
  any order, reads, writes, and destruction over per-cell occupancy with
  iterated guarded ownership, the end-to-end `arena_pipeline` over them, and
  `arena_reuse`, which frees the middle of three regions and places the next
  allocation of its size among the freed cells.
- `input-cursor/` verifies independently mutable cursors over a shared viewed
  input resource.
- `refcount/` verifies a heap reference count whose stored value equals its
  population of `reference(obj)` members, from initialization to final free.
- `shared-refcount/` shares one reference-counted object between its owner and
  two worker threads under a mutex.
- `bounded-pool/` verifies an object pool's original C with two populations
  under one control, including transfer between pools and cleanup.
- `jsonc-refcount/` verifies synthetic json-c-shaped field reads and writes on
  a small object.
- `jsonc-numeric/` verifies synthetic json-c-shaped `double` field reads and
  mixed integer/double scaling through pointer contracts and memory resources.
- `label-build-flags/` is the worked example of the own-project guide: a
  `Makefile` library whose `-I`/`-D` file is verified through a compiler
  import and whose `strlen` caller is verified directly, with an `extern`
  contract between them.
- `jsonc-existing-source/` preserves the upstream json-c version helper and
  proves its numeric and string results without editing the upstream C.
- `owned-string/` verifies a length-tracked string with a trailing terminator
  whose composite resource ties metadata to a mutable backing-memory content
  invariant.
- `owned-split-buffer/` verifies two adjacent, dynamically sized owned
  partitions and transfers an element between them by moving their boundary.
- `owned-segmented-buffer/` verifies an outer composite that contains two
  independently owned inner segment resources, including child mutation and
  metadata-only child permutation.
- `owned-vector/` verifies composite-resource state transitions over vector
  metadata and dependent backing storage.
- `vector-push/` verifies a general in-capacity vector append in a small,
  independently profiled proof unit.
- `runtime-int32-allocation/` verifies positive runtime-sized `int32` backing
  allocation and exact deallocation authority in isolation.
- `byte-representation/` copies a record holding a scalar and a pointer into a
  byte buffer and back with `memcpy`, proving the restored scalar, pointer
  identity, and pointee value without granting pointee authority, plus a
  parameterized companion and a modular caller.
- `allocated-linked-list/` combines fixed-size allocation authority with a
  recursive list resource, including failure-preserving prepend, one-node
  deallocation, and a terminating recursive destructor.
