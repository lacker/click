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

- `jsonc-refcount/` verifies field-level reads and writes on a small object.
- `owned-string/` verifies a length-tracked string with a trailing terminator
  whose composite resource ties metadata to a mutable backing-memory content
  invariant.
- `owned-vector/` verifies composite-resource state transitions over vector
  metadata and dependent backing storage.
