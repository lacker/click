# a wrapped loadable extent must not yield a real cell

A `loadable` range becomes a byte extent `(end - start) * width`, in modular
32-bit arithmetic. At `n == 1 << 30` with four-byte elements that product is
`1 << 32`, which is `0`, so `loadable(v[0..n])` claims an empty extent and is
vacuously true — provable for any pointer, from nothing but the value of `n`.
The cell rules used to read the same fact as "the elements `0..n`" and hand
back `v[0]`, four real bytes of an arbitrary pointer.

Every rule that reads an assumed extent at element granularity now asks first
whether that extent is a valid 32-bit byte extent — the same condition
`crate::kernel::memory_range_byte_count_guards` states wherever a contract
supplies a range, spelled over the range's element count so a proof can write
it. A stated range carries it; a range this proof merely proved, from the value
of `n`, does not.

The first theorem below is the true half: at `n == 1 << 30` the range really is
zero bytes, and claiming those bytes are loadable claims nothing. It stays here
because the vacuous premise being *free* is the setup, and it must keep
verifying for the second theorem to be the interesting one.

The second theorem is the false one. It proves that same vacuous fact itself
rather than assuming it, so it holds no valid-extent fact about `0..n`, and
reading `v[0]` through it is refused: the extent `n * 4` is not a valid one, so
reading it as `n` elements is not what the fact says. The order facts `0 <= 0`
and `0 < n` are both true and both stated, and they are still not enough. Its
`ensures` is deliberately trivial — the refusal is the cell read in the middle
of the proof, not the conclusion.

```click
theorem a_wrapped_extent_is_free(v: int32[], n: int32) {
    requires n == 1073741824;
    ensures n >= 0 and loadable(v[0..n]) by {
        have n >= 0 by { arithmetic() using { n == 1073741824; } }
        have loadable(v[0..n]) by { simp(); }
        split();
    }
}

theorem a_wrapped_extent_yields_a_cell(v: int32[], n: int32) {
    requires n == 1073741824;
    ensures n >= 0 by {
        have n >= 0 by { arithmetic() using { n == 1073741824; } }
        have loadable(v[0..n]) by { simp(); }
        have 0 <= 0 by { simp(); }
        have 0 < n by { arithmetic() using { n == 1073741824; } }
        have to_integer(v[0]) == to_integer(v[0]) by { simp(); }
        assumption();
    }
}
```

```expect
fail: it is not a valid 32-bit byte extent in this scope
```
