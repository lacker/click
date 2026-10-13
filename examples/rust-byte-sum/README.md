# Rust byte-slice sum

This synthetic example proves an unchanged Rust `while` loop sums arbitrary
input bytes. The result is an `i32`; the contract accepts slices of length
`0..=1000` and imposes no restriction on their byte values.

The `Integer` specification folds the input at function entry. A prefix-sum
invariant connects that specification to the accumulator. A mathematical
bound `0 <= total <= 255 * i` proves every signed addition is safe; the
native 64-bit `usize` counter retains checked indexing and increment checks.
The measure `bytes_len - i` proves termination. The contract views the input,
so the function has no authority to modify it.

The loop body's arithmetic is `have P by auto;`: the solver carries the
`uint64` and `int32` order facts to `Integer`, proves the addition defined,
observes each sum term by term, and closes each bound by a checked
certificate. What remains explicit is memory transport for the read and the
fold laws (`peel`).

The sidecar uses explicit low-word casts for the fold endpoints. Checked
full-width order and range premises justify those casts; truncation alone
never grants indexing authority. The proof covers empty input as well as
nonempty slices. This is a building block for the pinned checksum assessment,
not a proof of a checksum library.

Build the pinned Charon with `scripts/build-charon.sh --install-toolchain`, then run:

```sh
cargo run --bin click -- import lock examples/rust-byte-sum/sum.click
cargo run --bin click -- verify examples/rust-byte-sum/sum.click
cargo run --bin click -- profile examples/rust-byte-sum/sum.click
cargo run --bin click -- audit examples/rust-byte-sum/sum.click
```

Regression tests also reject a false sum, incorrect invariant, missing length
bound, and nondecreasing measure, and reverify the expanded proof.
