# Examples

This tree holds source fixtures that are larger than a single mdtest snippet.
Name directories after the domain and proof question, not after whether they
are "real" or "mini".

- Directories with matching mdtests are current verification targets.
- Directories ending in `-design` are concrete source/spec sketches for
  unresolved language or semantic questions. These are intentionally not
  required to pass today.

Most fixtures should stay small. Keep everything directly under `examples/`
unless there is a concrete reason to add hierarchy.
