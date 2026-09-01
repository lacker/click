# Extend the integer model beyond int32 and uint8

Found by the 2026-09-01 kernel audit at cb034b21 as the most frequently
reported functionality gap.

The kernel type universe is closed: `CType` is `Void`, `Int32`, `UInt8`,
`Int32Pointer`, `UInt8Pointer`, `Int32Array`, `UInt8Array`
(`src/kernel/primitives.rs:207-216`). Every arithmetic term is
`Bitvector32Term` (`primitives.rs:82-116`); every scalar comparison and
overflow condition in `ConditionTerm` is the signed variant
(`primitives.rs:133-143`); `uint8` is carried as an int32 term plus range
facts (`src/kernel/eval/expression.rs:45-48`). Conversion support is limited
to uint8 rvalue promotion and checked int32-to-uint8 narrowing; storing a
uint8-typed value into an int32 lvalue falls to the `_ => None` arm of
`coerce_c_value_to_type` (`expression.rs:53-90`) and becomes a
`TypeMismatch`. The Click parser accepts only the `int32` and `uint8` type
keywords (`src/surface/parser.rs:960-961`). `docs/internals/roadmap.md:83-86`
lists `int`, `size_t`, signed sizes, `uint32`, `uint64`, and well-specified
casts and promotions as remaining work.

Real C uses `size_t` in essentially every length and index computation,
`uint32_t`/`uint64_t` for bit manipulation, `long`/`int64_t` for offsets, and
`short`/`signed char` in headers. The roadmap's own pilot target, json-c,
stores numbers as `int64_t` and `double`.

## Violated invariant

Click should model the integer types real C programs declare, with C's
promotion and conversion rules, so that a function using `size_t` or
`uint32_t` can be verified without rewriting its declarations.

## Intended regression

A staged set of mdtests, each verifying a function that a C compiler accepts:

1. `unsigned char c` stored into an `int` local (uint8-to-int32 widening).
2. `unsigned int` arithmetic with wraparound: `uint32 add(uint32 a, uint32 b)`
   with `ensures result == a + b` under modular semantics, and an unsigned
   comparison that differs from the signed one.
3. `size_t`/`int64_t` length arithmetic: `size_t total(size_t n, size_t m)`
   with an overflow obligation, and indexing `p[i]` with `size_t i`.
4. A `short` field load and store with correct promotion.

Each stage lands with negative tests for the new UB and range obligations.

## Acceptance criteria

- The kernel term language and `CType` carry width and signedness for at
  least 8, 16, 32, and 64-bit integers; comparisons and overflow conditions
  exist in signed and unsigned forms; the LP64 ABI sizes and alignments are
  documented and tested against `repr(C)`.
- C integer promotions and usual arithmetic conversions are implemented in
  `eval` with obligations for lossy narrowing, matching ISO C for the
  supported types; uint8-to-int32 widening stores work.
- Surface Click contracts can name the new types and their literals.
- Existing int32/uint8 examples verify unchanged; the staged mdtests pass;
  `scripts/check.sh` passes.

Related: [c-type-spellings.md](c-type-spellings.md) for accepting the
standard spellings once the types exist;
[mathematical-integers-in-specs.md](mathematical-integers-in-specs.md) for
unbounded integers on the specification side.
