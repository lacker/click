# Reason about byte-width element indices

Found by the 2026-09-01 kernel audit at cb034b21.

`int32_element_index_from_offset` (`src/kernel/reasoning/path_facts.rs:210-237`)
yields an index only for `PointerOffsetTerm::Int32Scaled { byte_width: 4 }`
(`:226`) or a constant offset divisible by 4 (`:229`); a 1-byte-scaled index
falls to `_ => None` (`:235`). `int32_element_count_from_bytes`
(`:293-312`) likewise divides by 4 only. These helpers back common-base
pointer distinctness (`src/kernel/reasoning/memory_resolution.rs:1030-1079`),
the memory-DAG store-hop crossing (`src/kernel/memory_provenance.rs:1591-1607`),
and range membership, so `char*`/`uint8_t*` array subscripts and non-4-aligned
pointer arithmetic fall out of load resolution, framing, and separation
reasoning. Byte buffers are the dominant shape in parsers, protocol code,
and the roadmap's C-string work.

## Violated invariant

Click's memory reasoning should treat a byte-scaled index exactly as it
treats a 4-byte-scaled one: two stores to `buf[i]` and `buf[j]` with `i != j`
are distinct, a load at `buf[k]` transports across a store to `buf[i]` when
`k != i`, and `buf[0..n]` range membership follows from `0 <= k < n`.

## Intended regression

Kernel unit tests in `src/kernel/tests/memory_reasoning_tests.rs` mirroring
the existing int32 cases for `uint8` pointers: distinctness of `p + i` and
`p + j` under `i != j`; load transport across a byte store to a proven
different index; range containment of `p + k` in `[p, p + n)`. An mdtest
verifying a byte-buffer fill loop `while (i < n) { buf[i] = 0; i = i + 1; }`
with a postcondition over `buf[0..n]`, and one verifying a read of `buf[k]`
after a write to `buf[j]` with `j != k`.

## Acceptance criteria

- The index and count helpers are parameterized by element width (1, 4, and
  later 2 and 8) and every consumer passes the width of the access.
- The int32 behavior is unchanged; the uint8 tests above pass.
- `scripts/check.sh` passes.

Related: [integer-types.md](integer-types.md) adds the widths this must
generalize to.
