# Standard Library

The standard library currently lives in:

```text
stdlib/prelude.click
```

It is parsed as ordinary Click source by `src/lang/click.rs`. Standard-library
definitions are not hard-coded predicates or functions in the Click parser.

## Current Prelude

```click
function count(int32 p[], int32 lo, int32 hi, int32 x) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + if p[k] == x { 1 } else { 0 }
    })
}

predicate permutation(int32 a[], int32 b[], int32 lo, int32 hi) {
    forall (int32 x) {
        count(a, lo, hi, x) == count(b, lo, hi, x)
    }
}

function byte_count(uint8 bytes[], int32 lo, int32 hi, uint8 value) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + if bytes[k] == value { 1 } else { 0 }
    })
}

predicate bytes_equal(uint8 left[], int32 left_lo, uint8 right[], int32 right_lo, int32 len) {
    (0..len).all(|k| {
        left[left_lo + k] == right[right_lo + k]
    })
}

predicate bytes_equal_range(uint8 left[], uint8 right[], int32 lo, int32 hi) {
    (lo..hi).all(|k| {
        left[k] == right[k]
    })
}

predicate bytes_all_eq(uint8 bytes[], int32 lo, int32 hi, uint8 value) {
    (lo..hi).all(|k| {
        bytes[k] == value
    })
}

predicate bytes_contains(uint8 bytes[], int32 lo, int32 hi, uint8 value) {
    (lo..hi).any(|k| {
        bytes[k] == value
    })
}

predicate bytes_all_not_eq(uint8 bytes[], int32 lo, int32 hi, uint8 value) {
    (lo..hi).all(|k| {
        bytes[k] != value
    })
}

predicate cstr_prefix(uint8 bytes[], int32 len) {
    bytes_all_not_eq(bytes, 0, len, '\0')
}

predicate cstr_len(uint8 bytes[], int32 len) {
    0 <= len and cstr_prefix(bytes, len) and bytes_contains(bytes, len, len + 1, '\0')
}

predicate cstr(uint8 bytes[]) {
    exists (int32 len) {
        cstr_len(bytes, len)
    }
}

predicate cstr_bounded(uint8 bytes[], int32 max) {
    bytes_contains(bytes, 0, max, '\0')
}

theorem cstr_len_nonnegative(bytes: uint8[], len: int32) {
    requires cstr_len(bytes, len);

    ensures 0 <= len by {
        unfold(cstr_len);
        simp();
    }
}

theorem cstr_len_has_prefix(bytes: uint8[], len: int32) {
    requires cstr_len(bytes, len);

    ensures cstr_prefix(bytes, len) by {
        unfold(cstr_len);
        simp();
    }
}

theorem cstr_len_has_terminator(bytes: uint8[], len: int32) {
    requires cstr_len(bytes, len);

    ensures bytes_contains(bytes, len, len + 1, '\0') by {
        unfold(cstr_len);
        simp();
    }
}
```

`count` is a pure Click function over a range. `permutation` is a Click
predicate saying every `int32` value has the same count in both arrays over the
same half-open range. The array parameters are Click array refs, so callers can
write `permutation(p, old(p), lo, hi)` to compare current memory with
entry-state memory.

`byte_count` is the byte-oriented version of `count`. The byte predicates use
explicit half-open ranges or offset+length slices:

- `bytes_equal(left, left_lo, right, right_lo, len)` compares two byte slices
  with possibly different starting offsets.
- `bytes_equal_range(left, right, lo, hi)` compares the same half-open range in
  two byte arrays, including current-vs-old comparisons such as
  `bytes_equal_range(p, old(p), 0, n)`.
- `bytes_all_eq(bytes, lo, hi, value)` says every byte in a range is equal to a
  given `uint8` value.
- `bytes_contains(bytes, lo, hi, value)` says some byte in a range is equal to a
  given value.
- `bytes_all_not_eq(bytes, lo, hi, value)` says no byte in a range is equal to a
  given value.

The C-string predicates are still facts over C memory, not first-class Click
string values:

- `cstr_prefix(bytes, len)` says the first `len` bytes contain no terminator.
- `cstr_len(bytes, len)` says `len` is the exact spec length: no terminator
  before `len`, and a terminator at `len`.
- `cstr(bytes)` says some exact spec length exists. This matches a plain
  `char*`/`uint8*` API shape, but byte-level consequences still need enough
  memory-loadability facts when unfolded.
- `cstr_bounded(bytes, max)` says a terminator exists somewhere before `max`.
  This matches bounded scanning APIs.

The C-string projection theorems expose the public consequences of
`cstr_len(bytes, len)` without requiring user proofs to unfold the predicate:

- `cstr_len_nonnegative(bytes, len)` proves `0 <= len`.
- `cstr_len_has_prefix(bytes, len)` proves `cstr_prefix(bytes, len)`.
- `cstr_len_has_terminator(bytes, len)` proves
  `bytes_contains(bytes, len, len + 1, '\0')`.

These definitions are ordinary Click. They are not generic overloads and they
are not special kernel names.

## Kernel Support

The names `count` and `permutation` are library names, not kernel concepts.
However, the kernel has general term/proof support that makes these definitions
usable:

- `Bitvector32Term::RangeFold` represents symbolic folds.
- Bounded range `.all`/`.any` bodies lower under their range-membership facts,
  while the final kernel proposition keeps the explicit range guard.
- Small bounded forall facts can be instantiated when proving matching
  conditions.
- Empty folds simplify to the initial value.
- One-step folds substitute the item and accumulator once.
- Small concrete folds unroll.
- Symbolic folds compare equal modulo accumulator/item binder names.
- Count-shaped folds can be matched across a split range.
- Count sums are compared modulo addend order.

This is the intended pattern: keep definitions in Click where possible, and add
general proof support to the kernel only when the proof engine needs it.

## Namespace Behavior

Stdlib definitions are combined with user Click definitions during validation.
A user Click function, predicate, resource, or theorem cannot redefine a stdlib
name. A C function spec may still have the same name as a stdlib Click function
when there is no user Click definition conflict.

## Current Example

`mdtests/compare_swap2_permutation.md` proves that a two-cell compare-swap
preserves `permutation(p, old(p), 0, 2)` without copying the original values
into a separate snapshot array.

`mdtests/sort3_permutation.md` proves the same stdlib predicate for a three-cell
sorting network:

```click
permutation(p, old(p), 0, 3)
```

`mdtests/bubble_sort3_loop_permutation.md` proves the same predicate for a
loop-shaped fixed-size bubble sort using bounded execution.

`mdtests/loop_stdlib_permutation_invariant.md` proves the same predicate as a
direct loop invariant. The invariant and the postcondition both unfold
`permutation`; the unfolded `count` calls elaborate to pure fold terms over
explicit current and entry memory snapshots.

`mdtests/loop_old_count_invariant.md` is a focused regression for
`old(count(...))` inside a loop invariant. It checks that old-state pure
functions are elaborated through the same stdlib definition rather than through
a separate eager old-state evaluator.

`mdtests/byte_slice_stdlib.md` checks the first byte-slice layer:
`byte_count`, `bytes_equal`, `bytes_equal_range`, and `bytes_all_eq` over
`uint8[]` arrays.

`mdtests/byte_slice_range_predicates.md` checks `bytes_contains` and
`bytes_all_not_eq`, including `choose` over an explicitly unfolded existential
predicate requirement.

`mdtests/cstr_stdlib.md` checks the first C-string predicate layer:
`cstr_prefix`, `cstr_len`, `cstr`, and `cstr_bounded`. It also checks that C
function proof scripts can apply the `cstr_len` projection theorems.

`mdtests/stdlib_theorem_apply.md` checks that pure theorem proofs can apply
theorems from the standard library.

## Adding A Library Definition

1. Add the definition to `stdlib/prelude.click`.
2. Add an mdtest using it from an ordinary `.click` sidecar.
3. If the proof does not close, decide whether the missing support is:
   - a general kernel/prover law
   - a missing proof step
   - a language feature
   - a bad library abstraction
4. Update this document.

Avoid putting domain-specific definitions directly in the kernel just because
they are useful. Prefer stdlib definitions backed by general proof support.
