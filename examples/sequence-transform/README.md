# Sequence Transform

This synthetic project fixes a small ordinary C implementation for the
specification sequence type. The C is the implementation boundary: future
proof work must add sequence expressions, contracts, and tactics without
rewriting these functions into a verifier-specific form.

The functions isolate four sequence properties over fixed-size integer arrays:

- `sequence_copy3` preserves exact contents and order across two arrays;
- `sequence_concatenate2` joins two two-element inputs in left-to-right order;
- `sequence_reverse3` reverses a three-element input in place; and
- `sequence_contains3` observes sequence membership without mutation.

The intended specifications distinguish exact sequence equality from
permutation: reversing usually changes a sequence even though it preserves its
multiset, while copying preserves both. The concatenation function exercises
the associative sequence operation that later tree models will use to define
in-order traversal.

`sequence_transform.click` now verifies the finite-literal sequence slices
without changing the C: exact three-cell copying, fixed two-by-two
concatenation, in-place reversal, and exact membership observation. The
remaining symbolic range projection and first-class sequence-value work is tracked by
[`sequence-type.md`](../../issues/sequence-type.md).
