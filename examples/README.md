# Examples

This tree holds example projects that are larger than a single mdtest snippet.
Name directories after the domain and proof question, not after whether they are
"real" or "mini".

Each example project should contain ordinary `.c` or `.cpp` files and one or
more `.click` sidecars. The `tests/examples.rs` integration test verifies every
sidecar against its source. Compiler-import examples also include an
`*.click.import.json` configuration; a project-local `prepare.py`, when
present, prepares portable local inputs such as a compilation database before
the gate refreshes the import and verifies it.

Most fixtures should stay small. Keep everything directly under `examples/`
unless there is a concrete reason to add hierarchy.

## Source provenance

Examples have three distinct provenance classes:

- **Synthetic** fixtures are C or C++ written for this repository to isolate a
  language or proof-model question. Their source should still remain fixed while a
  proof is repaired, but they are not evidence that Click accepts unchanged
  third-party source.
- **C0 transcriptions** are semantics-preserving translations of identified C
  into Click's supported C0 subset. They must include a `SOURCE.md` naming the
  upstream source and revision and recording every translation.
- **Unchanged existing-source** fixtures preserve identified upstream files
  byte-for-byte. They must include a `SOURCE.md` plus a checked source-integrity
  manifest so proof work cannot silently edit the imported C.

Most projects in this tree are synthetic. In particular, `jsonc-refcount/` is
deliberately **json-c-shaped**, not copied from json-c. The
`jsonc-existing-source/` project is the first unchanged-source fixture; its
SHA-256 manifest is checked by the examples gate before verifying its numeric
version and version-string bytes under the explicit kernel target.

Current projects:

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
- `arena/` fixes the C0 implementation boundary for a first-fit allocator
  whose regions exercise user-defined suballocation and lifetime ownership.
  `arena_cells.click` verifies initialization, allocation anywhere, frees in
  any order, reads, writes, and destruction over per-cell occupancy with
  iterated guarded ownership, the end-to-end `arena_pipeline` over them, and
  `arena_reuse`, which frees the middle of three regions and places the next
  allocation of its size among the freed cells.
- `input-cursor/` verifies independently mutable cursors over a shared viewed
  input resource.
- `jsonc-refcount/` verifies synthetic json-c-shaped field reads and writes on
  a small object.
- `jsonc-numeric/` verifies synthetic json-c-shaped `double` field reads and
  mixed integer/double scaling through pointer contracts and memory resources.
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
