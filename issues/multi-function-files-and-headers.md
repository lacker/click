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

The first implementation slice accepts multiple function definitions and
compatible forward prototypes in one source. The next slice now resolves
quoted project-local includes from the named source bundle, recursively expands
their declaration text, and rejects function bodies in headers. System headers,
macros, conditional compilation, and other preprocessor handling remain open.
The follow-up slice now recognizes canonical whole-header guards and
`#pragma once`, suppressing repeated expansion of shared headers while keeping
arbitrary conditional compilation unsupported.
The modeled `<stdint.h>` system header is now accepted as a no-op because C0
already defines the semantics of its supported `int32_t` and `uint8_t` names;
other system headers remain unsupported. The first macro slice now accepts
object-like `#define NAME` replacements consisting of one supported integer or
character literal, expanding them in source order across a translation unit
and its included headers. The conditional-compilation slice now selects active
branches for `#if 0`, `#if 1`, `#if NAME` when `NAME` is a known 0/1 literal,
`#ifdef`, `#ifndef`, `#else`, and `#endif`, including nesting, while keeping
general preprocessor expressions unsupported. The follow-up conditional slice
now supports ordered `#elif` chains with the same bounded conditions and skips
conditions in branches that cannot be selected. The macro-state slice now
supports `#undef NAME`, including re-inclusion of a canonical guarded header
after its guard macro is undefined. The next conditional slice now supports
the exact `#if defined(NAME)`, `#if !defined(NAME)`, and corresponding `#elif`
forms, including whitespace around the operator and identifier. The boolean
conditional slice now combines those bounded atoms with `!`, `&&`, `||`, and
parentheses using normal precedence and short-circuit evaluation.

## Violated invariant

Click should verify a translation unit as C sees it: several functions per
file, prototypes, and the declarations reached through `#include`, so that a
real source file can be pointed at without splitting or editing it.

## Intended regression

An mdtest project with one `.c` file holding two functions (one calling the
other, declared before use by a prototype), a project-local header included
with `#include "types.h"` that holds the struct declarations, and a standard
header include (`#include <stdint.h>`) that is accepted and contributes only
the names Click already knows. A positive macro mdtest shares literal-only
object-like definitions from a local header across more than one source file.
Negative mdtests show that an unresolvable include or a multi-token/function-like
macro produces a positioned diagnostic naming the construct rather than
"unexpected character". A conditional-compilation mdtest includes unsupported
code and a missing include in an inactive branch, plus a negative test for a
general conditional expression.

## Acceptance criteria

- One `.c` file may define many functions; `verifying "file.c"` selects all
  of them and sidecar contracts attach by name.
- Function prototypes and forward references parse and resolve.
- `#include "local.h"` is resolved relative to the source and parsed for
  declarations; headers are supplied as named source-bundle dependencies and
  may not contain function definitions. Missing headers and include cycles
  receive source-named diagnostics.
- Canonical whole-header guards and `#pragma once` prevent repeated expansion
  when a shared header is reached through multiple include paths.
- `<stdint.h>` is accepted as a modeled no-op for the standard C0 type
  spellings; unknown system headers receive a source-named diagnostic.
- Object-like macros with one supported integer or character literal are
  expanded in source order across a translation unit and its included headers;
  uses in comments and quoted literals remain untouched, and redefinitions or
  other macro forms receive source-named diagnostics. `#undef NAME` removes a
  macro and permits a later literal redefinition.
- Function-like and multi-token macros, system headers other than the modeled
  `<stdint.h>`, comparisons, arithmetic, ternaries, and other general
  conditional expressions remain explicitly unsupported until a documented
  allowlist or preprocessor subset is implemented.
- The bounded conditional subset accepts `#if 0`, `#if 1`, `#if NAME` for a
  previously defined 0/1 literal macro, `#ifdef NAME`, `#ifndef NAME`, `#elif`
  with those same conditions, `#if defined(NAME)`, `#if !defined(NAME)`,
  and combinations of those atoms with `!`, `&&`, `||`, or parentheses. `#else`
  and `#endif` are also supported, including nested conditionals. Inactive
  branches are removed before C parsing, and malformed structure or
  unsupported active conditions receive source-named diagnostics.
- Shared struct declarations are reused across functions and files, replacing
  the per-file re-declaration in examples.
- `scripts/check.sh` passes.

Related: [global-variables.md](global-variables.md) for file-scope objects;
[external-function-contracts.md](external-function-contracts.md) for
callees with no body in the project.
