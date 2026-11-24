# a wrapped viewable span must not yield a real cell

A `viewable` range becomes a byte span `(end - start) * width`, in modular
32-bit arithmetic. At `n == 1 << 30` with four-byte elements that product is
`1 << 32`, which is `0`, so `viewable(v[0..n])` claims an empty span and is
vacuously true — provable for any pointer, from nothing but the value of `n`.
The cell rules used to read the same fact as "the elements `0..n`" and hand
back `v[0]`, four real bytes of an arbitrary pointer.

Every rule that reads an assumed span at element granularity now asks first
whether that span is a valid 32-bit byte span — the same condition
`crate::kernel::memory_range_byte_count_guards` states wherever a contract
supplies a range, spelled over the range's element count so a proof can write
it. A stated range carries it; a range this proof merely proved, from the value
of `n`, does not.

The first theorem below is the true half: at `n == 1 << 30` the range really is
zero bytes, and claiming those bytes are viewable claims nothing. It stays here
because the vacuous premise being *free* is the setup, and it must keep
verifying for the second theorem to be the interesting one.

The second theorem is the false one. It proves that same vacuous fact itself
rather than assuming it, so it holds no valid-span fact about `0..n`, and
claiming `defined(v[0])` through it is refused: the span `n * 4` is not a valid one, so
reading it as `n` elements is not what the fact says. The order facts `0 <= 0`
and `0 < n` are both true and both stated, and they are still not enough. Its
`ensures` is deliberately trivial — the refusal is the explicit read-validity claim in the middle
of the proof, not the conclusion.

```click
theorem a_wrapped_span_is_free(v: int32[], n: int32) {
    requires n == 1073741824;
    ensures n >= 0 and viewable(v[0..n]) by {
        have n >= 0 by { close() using { n == 1073741824; }; }
        have viewable(v[0..n]);
        close();
    }
}

theorem a_wrapped_span_yields_a_cell(v: int32[], n: int32) {
    requires n == 1073741824;
    ensures n >= 0 by {
        have n >= 0 by { close() using { n == 1073741824; }; }
        have viewable(v[0..n]);
        have 0 <= 0;
        have 0 < n by { close() using { n == 1073741824; }; }
        have defined(v[0]);
        close();
    }
}
```

```expect
fail: could not establish `defined(v[0])`
```
