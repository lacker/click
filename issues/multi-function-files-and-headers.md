# Accept multi-function files, prototypes, and includes

Found by the 2026-09-01 kernel audit at cb034b21.

The C0 grammar is "struct declarations then exactly one function definition"
(`src/languages/c/syntax.rs:806-830`, `:1808-1822` "each C source file holds
exactly one function"). The tokenizer has no arm for `#` or `"`
(`syntax.rs:1945-1972`), so every real file fails on its first `#include`.
There are no forward declarations or prototypes, and every callee's struct
declarations must be re-pasted per file (see `examples/jsonc-refcount/*.c`,
each redeclaring `struct json_object`). `docs/internals/roadmap.md:264-272`
lists the preprocessor as deferred.

The first implementation slice now accepts multiple function definitions and
compatible forward prototypes in one source. Header lookup, preprocessor
handling, and declaration sharing remain open here.

## Violated invariant

Click should verify a translation unit as C sees it: several functions per
file, prototypes, and the declarations reached through `#include`, so that a
real source file can be pointed at without splitting or editing it.

## Intended regression

An mdtest project with one `.c` file holding two functions (one calling the
other, declared before use by a prototype), a project-local header included
with `#include "types.h"` that holds the struct declarations, and a standard
header include (`#include <stdint.h>`) that is accepted and contributes only
the names Click already knows. A negative mdtest shows that an unresolvable
include or a macro definition produces a positioned diagnostic naming the
construct rather than "unexpected character".

## Acceptance criteria

- One `.c` file may define many functions; `verifying "file.c"` selects all
  of them and sidecar contracts attach by name.
- Function prototypes and forward references parse and resolve.
- `#include "local.h"` is resolved relative to the source and parsed for
  declarations; `#include <std.h>` for a documented allowlist is accepted
  without expansion; other preprocessor directives are rejected with a
  diagnostic (object-like `#define` constants may be supported as a
  documented subset).
- Shared struct declarations are parsed once and reused across functions and
  files, replacing the per-file re-declaration in examples.
- `scripts/check.sh` passes.

Related: [global-variables.md](global-variables.md) for file-scope objects;
[external-function-contracts.md](external-function-contracts.md) for
callees with no body in the project.
