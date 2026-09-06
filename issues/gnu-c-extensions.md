# Model the GNU C expression and declaration forms used by rbtree

Found by the 2026-09-04 MVR audit. The selected Linux rbtree translation unit
uses GNU-family constructs after preprocessing, including `typeof`, statement
expressions such as `({ ... })`, `__attribute__((aligned(sizeof(long))))`,
always-inline attributes, and branch-expectation builtins behind
`likely`/`unlikely`. Export and compiler headers may also contribute
declaration-only attributes and metadata.

Click now accepts `__attribute__((always_inline))` and
`__attribute__((__always_inline__))` as declaration-only metadata on supported
static inline helpers. Alignment and other semantic attributes remain open.

This issue is not permission to accept arbitrary GNU C by erasing unfamiliar
syntax. Each supported form needs an explicit C0 meaning or a checked
non-executable metadata classification.

## Violated invariant

Click should accept an unchanged source construct only when it models the
construct's value, effects, sequencing, type, layout, and relevant compiler
semantics. Compiler extensions must not be ignored when they can affect those
properties.

## Intended regression

Use unchanged focused C fixtures for:

1. a `typeof` temporary whose type is a pointer;
2. a statement expression that performs one ordered assignment and returns
   its final subexpression;
3. a struct alignment attribute whose low address bits are subsequently used;
4. `__builtin_expect` in a condition without changing the condition's value;
5. an unsupported executable attribute or builtin that is rejected rather
   than discarded.

The header inline regression also rejects an unsupported function attribute,
such as `aligned`, rather than treating it as harmless metadata.

The pinned rbtree translation unit must then parse with original source
locations and the modeled LP64 layout.

## Acceptance criteria

- The exact GNU forms needed by the pinned rbtree source and retained headers
  have documented syntax and semantics.
- `typeof` preserves complete modeled type metadata, including struct-pointer
  identity and qualifiers.
- Statement expressions preserve source-order evaluation, side effects, and
  the final value; they are not lowered by an unverified text rewrite.
- Supported alignment attributes affect the imported layout and allocation
  alignment used by proofs.
- Branch-expectation builtins preserve the operand's C value and effects.
- Ignorable attributes are restricted to an explicit declaration-only
  allowlist; the two supported always-inline spellings are accepted only on
  static inline helpers, while unknown or semantic attributes and builtins fail
  precisely.
- Focused positive and negative regressions, the rbtree parse regression, and
  `scripts/check.sh` pass.

Related: [kernel-scale-preprocessing.md](kernel-scale-preprocessing.md),
[pointer-integer-casts-and-tagging.md](pointer-integer-casts-and-tagging.md),
and [multiple-compilers.md](multiple-compilers.md).
