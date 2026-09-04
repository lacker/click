# Verify inline function definitions reached through headers

Found by the 2026-09-04 MVR audit. Click currently permits declarations in
included headers but rejects function bodies there. Linux `rbtree.h` and
`rbtree_augmented.h` contain essential `static inline` and
`static __always_inline` implementations. `lib/rbtree.c` calls those helpers,
including `rb_set_parent_color`, `__rb_change_child`, and
`__rb_erase_augmented`; treating them as unverified declarations would move
the core algorithm outside the proof.

## Violated invariant

A verified translation unit must include the semantics of inline function
definitions supplied by its headers, with C linkage and per-translation-unit
identity preserved.

## Intended regression

An unchanged project header defines two `static inline` helpers, one calling
the other, and is included by a `.c` file whose exported function calls the
outer helper. The complete call chain verifies. Including the same guarded
header through two paths does not create duplicate definitions, while two
translation units receive distinct internal-linkage instances.

A pinned rbtree import regression must resolve calls from `lib/rbtree.c` to
the actual inline bodies from the Linux headers rather than opaque contracts.

## Acceptance criteria

- Included headers may contribute supported inline function definitions as
  well as declarations.
- `static inline`, `extern inline`, and the selected GNU always-inline spelling
  have documented linkage and body-selection rules for the supported compiler
  profile.
- Repeated guarded inclusion does not duplicate a definition, and internal
  linkage remains translation-unit-local.
- Sidecar contracts attach to source-named inline functions without losing
  header source locations.
- Every called rbtree inline helper is either verified from its body or
  explicitly named as an external trust boundary; no helper becomes opaque
  merely because it came from a header.
- Positive linkage and duplicate-definition regressions and
  `scripts/check.sh` pass.

Related: [multi-function-files-and-headers.md](multi-function-files-and-headers.md)
and [kernel-scale-preprocessing.md](kernel-scale-preprocessing.md).
