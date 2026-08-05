# Examples

This tree holds example projects that are larger than a single mdtest snippet.
Name directories after the domain and proof question, not after whether they are
"real" or "mini".

Each example project should contain ordinary `.c` files and one or more
`.click` sidecars. The `tests/examples.rs` integration test verifies every
sidecar against the C files in the same directory.

Most fixtures should stay small. Keep everything directly under `examples/`
unless there is a concrete reason to add hierarchy.

Current projects:

- `input-cursor/` verifies independently mutable cursors over a shared viewed
  input resource.
- `jsonc-refcount/` verifies field-level reads and writes on a small object.
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
