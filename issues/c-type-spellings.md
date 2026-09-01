# Accept standard C type spellings and typedefs

Found by the 2026-09-01 kernel audit at cb034b21.

The C0 parser accepts only the invented spellings `void`, `int32`, `uint8`,
and `struct` as types (`src/languages/c/syntax.rs:964`; error at `:991-997`
"expected type `void`, `int32`, `uint8`, or `struct`"). `int`, `char`,
`unsigned char`, `int32_t`, `uint8_t`, `size_t`, `long`, `short`, and typedef
names are all rejected. No C file that compiles under a C compiler parses
under Click without rewriting every declaration, which the "existing C is the
verification boundary" doctrine in `CLAUDE.md` forbids. `examples/README.md:29`
notes that every example is synthetic and defers the first unchanged-source
fixture to [audit-existing-c-source-fidelity.md](audit-existing-c-source-fidelity.md).

## Violated invariant

Click should parse the type spellings real C source uses, mapping each to the
kernel type it denotes under the documented LP64 ABI, and should reject only
spellings that name a type the kernel cannot yet model.

## Intended regression

An mdtest whose C file uses `int`, `unsigned char`, `int32_t`, and `uint8_t`
(with the `<stdint.h>` names accepted as builtins even before headers are
supported) for parameters, locals, and struct fields, and verifies with a
sidecar that spells the same types. A second mdtest with `typedef struct S
S_t;` and `typedef int32_t idx_t;` used in declarations. Negative mdtests
showing that `long` and `size_t` produce a positioned "unsupported integer
width" diagnostic until [integer-types.md](integer-types.md) lands.

## Acceptance criteria

- `int` maps to int32, `unsigned char` and `uint8_t` to uint8, `int32_t` to
  int32, `char` to a documented choice (signed char is not modeled; either
  map to uint8 with a documented deviation flag, or reject with a diagnostic
  naming the fix).
- `typedef` of struct and integer types is accepted and resolved in the
  parser; typedef names participate in struct-pointer resolution.
- Surface Click sidecars accept the same spellings.
- The C0 reference (`docs/reference/language/c0.md`) documents the accepted
  spellings and the ABI mapping; `scripts/check.sh` passes.
