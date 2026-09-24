# Byte representation

The byte-representation milestone has landed. Its verified program, the frozen
[`rep_copy.c`](../../examples/byte-representation/rep_copy.c), now lives in the
[`examples/byte-representation/`](../../examples/byte-representation/README.md)
project with a parameterized companion and a modular caller, and
`tests/examples.rs` pins its bytes there. The selected profile (the default
LP64 little-endian kernel target, `sizeof(struct record) == 16`, and the
standard-library `memcpy` declaration with its checked representation-copy
effect) is recorded in the example's README.

The semantics relating bytes and typed cells, the copy effect's refusals, the
byte view, the negatives, and the scaling regressions are in the design
record, [Byte representation](../../docs/internals/byte-representation.md).
