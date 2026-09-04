# Extend the integer model beyond int32 and uint8

Found by the 2026-09-01 kernel audit at cb034b21 as the most frequently
reported functionality gap.

The kernel type universe originally stopped at `CType::UInt8`; every scalar
comparison and overflow condition was signed, and `uint8` was carried as an
int32 term plus range facts. The first integer conversion slice added uint8
rvalue promotion, uint8-to-int32 widening, and checked int32-to-uint8
narrowing. The current slice adds scalar `CType::UInt32` with 32-bit storage,
`uint32`/`uint32_t`/`unsigned int` spellings, modular arithmetic and bitwise
operators, typed shifts, and unsigned ordered comparisons.

Real C uses `size_t` in essentially every length and index computation,
`uint32_t`/`uint64_t` for bit manipulation, `long`/`int64_t` for offsets, and
`short`/`signed char` in headers. The roadmap's own pilot target, json-c,
stores numbers as `int64_t` and `double`.

## Violated invariant

Click should model the integer types real C programs declare, with C's
promotion and conversion rules, so that a function using `size_t` or
`uint32_t` can be verified without rewriting its declarations.

## Progress

The first conversion slice now supports the existing C0 `uint8` value widening
to `int32` at assignment and function-return boundaries. The conversion keeps
the underlying checked 32-bit term while changing its C type tag; the existing
checked `int32`-to-`uint8` narrowing rule remains unchanged. The regression is
`mdtests/uint8_widening.md`.

The second slice now supports scalar `uint32` values in parameters, returns,
locals, assignments, and Click contracts. `uint32`/`uint32_t`/`unsigned int`
source declarations share a four-byte LP64 representation. Addition,
subtraction, and multiplication wrap modulo 2^32; division and remainder use
unsigned semantics; equality compares the bit pattern and ordered comparisons
use unsigned order. Bitwise operators preserve the raw 32-bit pattern, right
shifts are logical, and prefix/postfix updates and compound assignments use the
same operator semantics. Pointers, arrays, and struct fields remain
intentionally outside this slice. The regressions are
`mdtests/uint32_arithmetic.md`, `mdtests/uint32_operators.md`,
`mdtests/uint32_division_by_zero.md`, and `mdtests/uint32_invalid_shift.md`.

The third slice now supports scalar signed and unsigned 16-bit values:
`short`/`signed short`/`int16_t` map to `int16`, while `unsigned short` and
`uint16_t` map to `uint16`. Both use two-byte LP64 storage and promote to
`int32` for arithmetic, comparisons, shifts, and bitwise operators. Checked
casts and assignment/return conversions enforce `int16`'s
`-32768..32767` range and `uint16`'s `0..65535` range. The regression is
`mdtests/int16_uint16_conversion.md`. Pointer, array, `size_t`, and 64-bit
forms were separate work at this stage; the scalar 64-bit forms are covered
by the next slice below.

The fourth slice now supports scalar signed and unsigned 64-bit values:
`long`/`long long`/`int64_t` map to `int64`, while `unsigned long`,
`unsigned long long`, `uint64_t`, and `size_t` map to `uint64`; `ssize_t` is
also accepted as the signed 64-bit alias. Both use eight-byte LP64 storage.
Signed arithmetic and left shifts retain C undefined-behavior obligations,
unsigned arithmetic wraps modulo 2^64, comparisons preserve signedness, and
bitwise operations and shifts cover both 64-bit representations. C integer
literal suffixes now select their width and signedness instead of being
discarded. The positive and negative regressions are
`mdtests/int64_uint64_arithmetic.md`, `mdtests/int64_division_by_zero.md`,
`mdtests/int64_invalid_shift.md`, `mdtests/int64_signed_overflow.md`, and
`mdtests/uint64_division_by_zero.md`. Scalar struct fields are covered by
`issues/struct-model.md`.

The fifth slice extends the same width and signedness model through data
pointers, pointer arrays, fixed-size local arrays, array parameters, and the
`malloc`/`calloc`/`realloc` paths. Pointer offsets preserve the declared
pointee width, and `size_t` indices remain 64-bit through dynamic indexing.
Heap sizes may be written as exact 64-bit expressions when contract facts
reduce them to Click's checked memory-block extent. The regressions are
`mdtests/integer_pointer_array_widths.md`,
`mdtests/integer_heap_widths.md`, `mdtests/pure_theorem_integer_width_arrays.md`,
and the corrected `mdtests/uint32_pointer_rejected.md`.

## Intended regression

A staged set of mdtests, each verifying a function that a C compiler accepts:

1. `unsigned char c` stored into an `int` local (uint8-to-int32 widening).
2. `unsigned int` arithmetic with wraparound: `uint32 add(uint32 a, uint32 b)`
   with `ensures result == a + b` under modular semantics, unsigned
   multiplication/division/remainder and bitwise/shift coverage, and an
   unsigned comparison that differs from the signed one.
3. `size_t`/`int64_t` length arithmetic: `size_t total(size_t n, size_t m)`
   with an overflow obligation, and indexing `p[i]` with `size_t i`.
4. A `short` field load and store with correct promotion.
5. `size_t`/64-bit length arithmetic and indexing through local arrays,
   pointer parameters, and width-preserving heap allocations.

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
