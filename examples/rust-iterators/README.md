# Rust slice iterator sum

The unchanged `sum.rs` uses `for &byte in bytes` to sum arbitrary input bytes.
Its contract accepts lengths `0..=1000`, including empty input, and proves an
exact mathematical sum of the bytes at function entry. The sidecar chooses a
prefix invariant and bounds each intermediate sum by 255 times that prefix's
length.

The iterator is held as the slice it still covers (`docs/reference/rust.md`,
Slice iterator loops): each pass's `next()` yields the element at
`iter.as_slice()` and moves the slice on by one, as `core`'s does. The proof
observes the iterator through Rust's own methods, `iter.len()` and
`iter.as_slice()`, and carries where it stands as an invariant,
`iter.as_slice().as_ptr() == bytes.as_ptr() + (bytes.len() - iter.len())`. The
`maintain` script splits on `0u64 < iter.len()`; the copied pattern reads the
yielded address, and an exhausted iterator performs no read.

The sidecar uses Integer specification arithmetic,
so it imports no library bridge: the contract and invariants compare exact
Integers, and the body's arithmetic is `have P;`. The prefix length
`bytes.len() - iter.len()` is also a `usize` value, used as a fold
endpoint and an index. Facts about that machine value are written as
Integer observations, `to_integer(bytes.len() - iter.len()) < 18446744073709551615`,
which is the same fact as the native bound (see "One form for comparisons of
observations" in `docs/internals/mathematical-integers.md`), so `unfold` and
indexing use it directly. A plain `bytes.len() - iter.len()` in
a comparison is Integer subtraction.

No processed count or index is supplied by default. This sidecar explicitly
derives its prefix length as original slice length minus remaining length. It
retains views of the input and uses remaining
length as its decreasing measure.

Immutable shared byte-slice bindings support copied byte patterns and shared
reference variables, directly or through `.iter()`. The
[reference iterator example](../rust-iter-references/README.md) proves a sum
using yielded references. Shared scalar array iteration still uses the importer's older iterator state; stored `.chunks_exact()`
iterators still hold a cursor and remaining length; see the [exact-chunk example](../rust-chunks-exact/README.md).
This fixture covers immutable shared bytes. The pinned checksum libraries remain unverified.

Build the pinned Charon with `scripts/build-charon.sh --install-toolchain`, then run:

```sh
cargo run --bin click -- import lock examples/rust-iterators/sum.click
cargo run --bin click -- verify examples/rust-iterators/sum.click
cargo run --bin click -- profile examples/rust-iterators/sum.click
cargo run --bin click -- audit examples/rust-iterators/sum.click
```

Regression tests reject false results, incorrect invariants, missing bounds,
nondecreasing measures, and unsupported iterator forms. They also verify the
expanded proof through the ordinary CLI.
