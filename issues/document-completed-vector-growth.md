# Remove stale claims that vector growth is pending

## Problem

The focused vector-push and runtime-allocation READMEs still say that
malloc-copy-free vector growth is pending and link to
`issues/owned-vector-runtime-growth.md`. That issue was deleted when verified
growth landed in `examples/owned-vector`.

The higher-level example and memory-model documentation describe the completed
feature correctly, so the repository currently gives contradictory guidance
depending on which focused example a reader opens.

## Required update

- Update `examples/vector-push/README.md` to say that allocation-aware growth is
  verified in `examples/owned-vector`, while this project remains the focused
  independently profiled in-capacity append.
- Update `examples/runtime-int32-allocation/README.md` to say that its allocation
  resource is composed into owned-vector growth, while this project remains the
  minimal allocation/free fixture.
- Remove every link or textual reference to the deleted runtime-growth issue.
- Keep the documented boundaries precise: growth is `old_cap + 1`, runtime
  allocation is the positive bounded `int32` slice, and broader allocators or
  `realloc` remain unsupported.

## Acceptance criteria

- Searching documentation finds no claim that owned-vector growth is pending
  and no link to `owned-vector-runtime-growth.md`.
- Both focused READMEs link readers to the checked owned-vector example.
- The focused purpose of each project remains clear and no unsupported general
  allocation or geometric-growth claim is introduced.
- Documentation links pass the existing book/link checks, if present.
