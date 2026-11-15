# Shared scalar array lengths

`arrays.rs` and `arrays.click` are byte-for-byte copies of the existing
`examples/rust-arrays` source and sidecar. The whole sidecar verifies through
Charon, including shared length, signed indexing, mutation, empty arrays, and
frame preservation. Only the import configuration switches backends.

`bounds.rs` is a synthetic scaling checkpoint: lengths of empty `u32`,
1024-element `i32`, and million-element `u32` arrays verify without element
views or ownership. Length reads paired metadata, so it does not allocate
array elements or claim authority to read their bytes. Deterministic tests
check equal lowered statement count and bounded proof work across those sizes.

Rust resolves `.len()` after shared array-to-slice coercion to `LangItem::SliceLen`.
`shared-scalar-slice-length-v1` accepts the existing shared byte slice or a
shared `i32`/`u32` scalar slice with matching instantiated element type. The
adapter still checks the nonlocal declaration identity, safe Rust ABI, arity,
generic slice signature, and `usize` result/destination. Mutated artifacts
with a missing identity, local or unsafe declaration, wrong signature, or
mismatched element are rejected. Unsupported `u16` arrays remain rejected.

The new semantic entry changes import identities; existing checkpoint locks
have been updated with the same compiler and extractor pins. Existing ULLBC
bytes are retained where a fresh extraction differed only in its temporary
destination path. External Charon locks require explicit refresh.

Regression coverage uses the shared verification engine for positive and
false-length claims, and rechecks `verify`, `profile`, `audit`, and expanded
certificates. The required live Charon gate re-extracts both checkpoints and
rejects a conflicting Rust borrow and unsupported element width.

```sh
scripts/check.sh --charon-live
cargo nextest run --lib --test rust_import -E 'test(charon_scalar_) | test(charon_array_lengths)'
```

This closes `rust-arrays` in the unchanged-fixture inventory. The subsequent
array-value increments corrected its misleading signature diagnostic and added
compact borrowed states; `rust-array-values` now verifies unchanged too.
Current fixture parity is 10/16 (62.5%), with 14/16 (87.5%) importing.
