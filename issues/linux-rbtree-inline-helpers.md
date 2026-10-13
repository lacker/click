# Verify Linux rbtree inline helpers from the pinned headers

Priority: P2.

Soundness: incomplete. The pinned translation unit does not import yet, so
no helper is verified or assumed. The acceptance criteria forbid treating a
header helper as opaque.

The header-inline mechanism is landed: supported `static inline` and
`static __always_inline` definitions reached through headers parse with
translation-unit-local linkage, accept sidecar contracts by ordinary C
spelling, are called through that contract when they have one and execute
their checked bodies at call sites when they do not, and attribute bundle
diagnostics to `header.h:line`
(`docs/reference/language/c.md`,
`docs/reference/language/limitations.md`; regressions
`mdtests/inline_functions_in_headers.md`,
`mdtests/always_inline_functions_in_headers.md`,
`mdtests/inline_helper_sidecar.md`,
`mdtests/inline_header_error_location.md`,
`mdtests/conflicting_inline_helpers_across_headers.md`,
`mdtests/duplicate_inline_helpers_across_headers.md`).
What remains is the instantiation that motivated it: the actual inline
helpers in Linux `rbtree.h` and `rbtree_augmented.h` as called from the
pinned `lib/rbtree.c` (`rb_set_parent_color`, `__rb_change_child`,
`__rb_erase_augmented`, `rb_link_node`, `rb_set_parent`, and the other
called helpers). Treating them as unverified declarations would move the
core algorithm outside the proof.

This is blocked on the remaining
[kernel-scale-preprocessing](kernel-scale-preprocessing.md) packages. The
first importer milestone is landed and the pinned input closure is checked in
at `integrations/linux-rbtree/`, but the pinned translation unit does not
import yet. `typeof`, statement expressions, and `__builtin_expect` are
already modeled and are not what stops it. The measured rejections inside
the rbtree declarations are the kernel's `inline` attributes, unnamed
prototype parameters, the export declarations and assembly,
`compiletime_assert`'s block-scope declarations, `__builtin_constant_p`, a
few const and conditional-type forms, and one static non-inline function;
that issue lists them with locations. Importer, manifest, and general
GNU-form work belongs to that issue, not this one.

## Violated invariant

A verified translation unit using the pinned Linux rbtree headers must
include the semantics of the actual inline bodies those headers supply;
no called helper may become opaque merely because it came from a header.

## Intended regression

A pinned regression imports the unchanged `lib/rbtree.c` plus the public
inline implementations reached through its headers through the
compiler-import route and resolves every called inline helper to its
header body (or names it as an explicit external trust boundary). The
helpers execute at their call sites under the landed mechanism; the
regression checks the expected helper inventory and successful
parsing/lowering of the retained input with original-source diagnostics.
It must not change upstream `.c` or headers, substitute
verifier-friendly macro bodies, or bless forged output.

## Acceptance criteria

- Every inline helper called from the pinned `lib/rbtree.c` is either
  verified from its body or explicitly named as an external trust
  boundary; no helper is opaque merely because it came from a header.
- The import uses the validated compiler-import route with original file
  and line attribution and unchanged translation-unit linkage identity.
- `extern inline`, richer inline signatures, and broader GNU alignment
  forms remain explicitly deferred, not silently accepted.
- Focused positive/negative regressions and `scripts/check.sh` pass;
  fixture provisioning follows the preprocessing issue's reproducibility
  contract (no downloads inside the gate, no silent skips).

Related: [kernel-scale-preprocessing.md](kernel-scale-preprocessing.md)
(importer, manifest, retained C semantics, and fixture provisioning) and the
[supported GNU C forms](../docs/reference/language/c.md#supported-expressions-and-statements)
(GNU form semantics).
