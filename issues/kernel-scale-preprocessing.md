# Import kernel-scale preprocessed translation units

Found by the 2026-09-04 minimum-viable-rbtree (MVR) audit of Linux
`lib/rbtree.c` and its public headers.

Click's source-bundle preprocessor intentionally supports a small subset:
project-local includes, one modeled system header, literal object macros,
bounded conditionals, and function-like macros with at most three parameters.
The Linux rbtree translation unit depends on the configured kernel include
graph, compiler predefined macros, multi-token object macros, macros with more
than three parameters, token pasting, and nested rescanning. Reimplementing
enough of the C preprocessor ad hoc would make Click disagree with the compiler
that actually builds the verified source.

MVR targets one pinned Linux revision, compiler, configuration, and LP64
target. Supporting a target matrix remains in
[multiple-compilers.md](multiple-compilers.md); this issue only establishes a
faithful import boundary for that one configuration.

## Violated invariant

The C declarations and function bodies Click verifies must be the same active
translation unit selected by the configured compiler. Unsupported
preprocessor syntax must not force edits to `lib/rbtree.c` or silently select a
different conditional branch.

## Intended regression

Check in a reproducible manifest for a pinned Linux `lib/rbtree.c` translation
unit. The manifest names the source revision, compiler identity, target,
include roots, and preprocessing flags. Import the compiler-preprocessed
source while retaining line-marker provenance back to `lib/rbtree.c` and the
included headers. Changing a relevant define or supplying stale output must be
rejected.

A focused fixture must exercise a macro with more than three parameters,
token pasting, nested rescanning, a compiler predefined condition, and a
system include selected from configured include roots.

## Acceptance criteria

- A project can import compiler-preprocessed C from a reproducible manifest
  tied to exact source, compiler, target, include, define, and flag inputs.
- Preprocessing handles the Linux rbtree include graph and macro uses without
  changing the upstream `.c` or headers.
- Diagnostics and proof locations map through line markers to the original
  source and header paths.
- A mismatched or stale manifest is rejected before verification.
- Preprocessing is not trusted for C execution semantics: Click still parses
  and lowers every retained executable construct.
- Declaration-only kernel metadata may be omitted only by a documented,
  checked projection that cannot remove executable code or storage effects.
- The focused regressions, the pinned rbtree import regression, and
  `scripts/check.sh` pass.

Related: [multi-function-files-and-headers.md](multi-function-files-and-headers.md),
[gnu-c-extensions.md](gnu-c-extensions.md), and
[multiple-compilers.md](multiple-compilers.md).
