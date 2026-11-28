# Rust slice iterator references

The unchanged `sum.rs` uses `for byte in bytes.iter()` and reads each yielded
shared reference with `*byte`. The contract proves the exact mathematical sum
of arbitrary input bytes at function entry for lengths `0..=1000`, including
empty input, with safe additions and termination.

The Charon adapter checks the resolved standard core slice `.iter()` method and
compiler iterator desugaring. The artifact retains the iterator operation rather
than rewriting it into an index loop. The iterator is held as the slice it
still covers (`docs/reference/rust.md`, Slice iterator loops): a successful
`next()` yields `iter.as_slice().as_ptr()` and leaves a remaining slice that starts
one element later and is one shorter. No generated local is named. Dereferencing the yielded reference requires
input views; Rust rejects writing through it.

The proof carries where the iterator stands as an invariant,
`iter.as_slice().as_ptr() == bytes.as_ptr() + (bytes.len() - iter.len())`, and bounds
each sum by 255 times the prefix length `bytes.len() - iter.len()`.
`let { result: loaded_byte } = step();` names the checked scalar read. The
remaining length `iter.len()` ranks the loop. An empty iterator exits without
reading.

This fixture covers immutable shared bytes. The pinned checksum libraries remain unverified.

Build the pinned Charon with `scripts/build-charon.sh --install-toolchain`, then run:

```sh
cargo run --bin click -- import lock examples/rust-iter-references/sum.click
cargo run --bin click -- verify examples/rust-iter-references/sum.click
cargo run --bin click -- profile examples/rust-iter-references/sum.click
cargo run --bin click -- audit examples/rust-iter-references/sum.click
```

Regression tests reject false results, missing length bounds, missing views,
nondecreasing measures, unsupported iterators, and writes through shared
references. They also verify the expanded proof through the ordinary CLI.
