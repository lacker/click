# Linux augmented rbtree entry points

These sidecars connect the public augmented entry points to the separately
verified insertion, splice, and color-repair contracts. The wrapper definitions
are extracted verbatim from Linux v6.8.12 in
[`input-closure.tar.gz`](../../integrations/linux-rbtree/input-closure.tar.gz):
`__rb_insert_augmented` and `__rb_erase_color` come from `lib/rbtree.c`;
`rb_insert_augmented` and `rb_erase_augmented` come from
`include/linux/rbtree_augmented.h`. The insertion implementation is the
unchanged existing extract; the erase implementation includes the existing splice and repair extracts. Both reuse
the plain insertion example's header shim. The dummy callbacks and plain
wrappers remain available for imported contracts. Source licensing is
GPL-2.0-or-later.

`rbtree_insert_augmented.click` checks both insertion wrappers. The callback is
supplied directly or read through a borrowed const table field. The result is
a balanced root with consistent parents and the original in-order contents.

`rbtree_erase_color.click` checks the exported repair wrapper.
`rbtree_erase_leaf.click` checks the public erase wrapper for red and black leaf
deletion at any position. It calls repair exactly when the splice returns a
nonnull deficit parent. The result has the exact repaired model, consistent
parents, preserved remaining in-order contents, and detached-node ownership.

`rbtree_subtree_size.click` starts a concrete augmentation model. Its mathematical
size is nonnegative and unchanged by reparenting. Both rotation theorems prove
that the promoted root retains the original size and the demoted root has one
plus the sizes of its new children. This justifies copying the old root's
summary and recomputing the demoted node. Connecting those mathematical values
to C metadata fields, including machine-integer bounds, remains unfinished.

The C frontend checks the type query, static assertion, and member offset used
by Linux `container_of`; unsigned pointer subtraction preserves the offset and
GNU `void*` arithmetic uses byte steps. The unchanged macro's first-member
address recovery is verified in [`c_container_of.md`](../../mdtests/c_container_of.md).

`rbtree_size_copy.click` verifies the unchanged generated copy callback in
`rbtree_size_copy.c`. Its `size_metadata` resource ties the owned C size field to
an `int32` model value. Copy preserves the source resource and returns target
metadata equal to the source's entry value. The `CopySize` callback contract
expresses this transition; `sized_copy_has_size_contract` certifies the concrete
static-inline function through an execution theorem with explicit resource maps.
Explicit contract casts through `void*` describe the enclosing node. This establishes metadata transport, not
that the value counts a subtree: rotation/recomputation, propagation and its
loop measure, machine-integer bounds, and the tree/metadata invariant remain.
The copy body is extracted separately from the full callback table; integrating
that table also requires termination evidence for its propagation callback.

This is an entry-point integration increment of
[chunk 14](../../issues/rbtree-example.md#augmented), not the completed
augmentation proof. Imported callback contracts currently have no writable
footprint. Mutation-capable metadata callbacks and an augmentation invariant
remain to be connected to the implementation proofs. Each imported module is
verified separately; importing its contract does not rerun its proof.

Run `click verify examples/rbtree-augmented` to check these entry points.
