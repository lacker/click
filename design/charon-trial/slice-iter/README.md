# Slice iterator through its remaining slice

`sum.rs` is a byte-for-byte copy of `examples/rust-iter-references/sum.rs`:
`for byte in bytes.iter()` summing the bytes it reads through each yielded
reference. The iterator is held as the slice it still covers, read through
`iter.as_slice()` and `iter.len()`, and no generated local is named.

`sum.click` proves the same contract as the example: the exact mathematical
sum of the input bytes for lengths `0..=1000`. The loop carries where the
iterator stands as an ordinary invariant,
`iter.as_slice().as_ptr() == bytes.as_ptr() + (bytes.len() - iter.len())`. Each `next()`
moves the remaining slice on by one element and shortens it by one; the
proof carries the invariant across it with one pointer-association theorem
it states itself.

The native Charon artifact and import lock are committed for offline checks.
The nightly test `charon_slice_iter_sums_bytes_by_its_library_contract`
verifies the proof and rejects a missing view, a false result, a shifted
position invariant, a wrong step and a non-decreasing measure.

The base case is proved at the literal `0u64`: the proof first states
`bytes.len() - loop(0).iter.len() == 0u64` and rewrites with it.
The tools test `charon_slice_iter_tools_recheck_expanded_certificate`
expands and re-verifies the proof.
