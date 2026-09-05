# Examples

This tree holds example projects that are larger than a single mdtest snippet.
Name directories after the domain and proof question, not after whether they are
"real" or "mini".

Each example project should contain ordinary `.c` files and one or more
`.click` sidecars. The `tests/examples.rs` integration test verifies every
sidecar against the C files in the same directory.

Most fixtures should stay small. Keep everything directly under `examples/`
unless there is a concrete reason to add hierarchy.

## Source provenance

Examples have three distinct provenance classes:

- **Synthetic** fixtures are C written for this repository to isolate a
  language or proof-model question. Their C should still remain fixed while a
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
SHA-256 manifest is checked by the examples gate, while its parser-only status
records the current C0 boundary.

Current projects:

- `sequence-transform/` fixes small array copy, concatenation, reversal, and
  membership operations for the specification sequence type; its sidecar
  currently imports the C without claiming the missing sequence contracts.
- `modeled-binary-tree/` fixes a plain binary-tree implementation for the
  heap-derived in-order sequence model, membership, rotation-preservation, and
  structural-termination work required by MVR; its sidecar currently imports
  the C without claiming those proofs.
- `arena/` fixes the C0 implementation boundary for a first-fit allocator
  whose regions will exercise user-defined suballocation and lifetime
  ownership; its current sidecar is a parser-only scaffold tracked by the
  arena resource-ownership issue.
- `input-cursor/` verifies independently mutable cursors over a shared viewed
  input resource.
- `jsonc-refcount/` verifies synthetic json-c-shaped field reads and writes on
  a small object.
- `jsonc-existing-source/` preserves the upstream json-c version helper and
  reports its checked parser-only qualification.
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
- `allocated-linked-list/` combines fixed-size allocation authority with a
  recursive list resource, including failure-preserving prepend, one-node
  deallocation, and a terminating recursive destructor.
