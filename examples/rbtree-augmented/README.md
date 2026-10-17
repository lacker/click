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
summary and recomputing the demoted node. The concrete recomputation proof below establishes the bounded machine sum;
the recursive metadata invariant below supplies the mathematical connection;
the concrete callbacks restore this invariant through recomputation, rotation,
and arbitrary ancestor propagation. Connecting writable callbacks to the
augmented entry points remains unfinished.

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
Explicit contract casts through `void*` describe the enclosing node. This
establishes scalar metadata transport. The recursive invariant and its
restoration through arbitrary ancestor propagation are described below.
The copy body is extracted separately from the full callback table. The full
propagation proof below also provides its checked termination evidence.

`rbtree_size_compute.click` verifies a concrete recomputation helper with the
existing Linux `rb_entry` macro. Its optional child metadata resources carry
zero for null children. For all four child configurations it preserves the
children and sets the parent to one plus their entry sizes, including the
early return when the stored size already agrees. The contract records that
a nonzero result means the entry size already equals the recomputed sum. `size_arithmetic.click`
proves the signed additions defined from nonnegative sizes and a bounded sum.
`ComputeSize` describes the helper as a callable metadata contract, and
`compute_size_has_size_contract` proves it for all four child configurations.
Its guarded separation premises keep each borrowed child-pointer field apart
from either child's writable metadata. `child_size_separation` derives those
premises from ownership of the parent's `rb` prefix and a nonnull child's
metadata, using the existing partition rule. The callback proof also applies
the checked sum-definedness lemma before the call so the returned size equality
has both arithmetic guards available.

`rbtree_size_rotate.click` verifies the unchanged `RB_DECLARE_CALLBACKS`
rotation body specialized for this node type. It copies the old root's entry
metadata into the promoted root, then calls `compute_size` to recompute the
demoted root from its children. Both child models are preserved. `RotateSize`
and its execution theorem provide the callable interface, for all four nullable
child configurations. The shared `rbtree_size.h` keeps the node type and
`container_of` definitions separate from the C bodies; each sidecar explicitly
lists the C dependencies of its imported contracts.

`rbtree_size_model.click` defines the recursive `SizedTree` model and its
`sized_at` ownership resource. `sized_shape` erases metadata into the existing
`RbTree` model. Each node owns its links, parent tag, size metadata, and two
child resources, with an integer equation relating its stored size to the
children's stored sizes. `certify_size` is a checked recursive proof procedure:
it preserves ownership and the model and establishes that the root's stored
size equals the mathematical subtree count and that all model counts satisfy
the recursive size equation. Its recursive calls use the strict
subtree-count descent proved by `sized_child_descent`. `size_sum_as_integer`
connects a defined machine sum to the corresponding mathematical integer sum.

`rbtree_size_recompute_model.click` connects the unchanged `compute_size` helper
to the recursive invariant. Its dirty-root resource owns the root metadata and
two valid children, without assuming the root count is already correct.
`RecomputeTree` bounds the child sum, preserves the erased tree shape, and
returns a valid `sized_at` tree whose stored size equals its mathematical
subtree count, while preserving both child models. The execution theorem checks
all four nullable-child cases. A nonzero return also certifies that the cached size was already correct, which is the fact
propagation needs to justify its early stop.

`rbtree_size_rotate_model.click` connects the unchanged `sized_rotate` callback
to the recursive invariant for both rotation directions and all four nullable
child configurations. The links and parent tags have already rotated; the
promoted summary is stale and the demoted summary still holds the original
subtree's total. The callback returns a valid `sized_at` tree, preserves the
erased shape, and restores the mathematical subtree count. `RotateTreeLeft`
and `RotateTreeRight` expose these checked callable contracts.
The nightly fixture `tests/fixtures/proof-expansion/rbtree-return-pointer-lemma.click` retains the
left rotation's imported `sized_parent_is_shape` applications after the C call,
including their struct-pointer and recursive-model arguments. Its selected
closer is also checked after expansion and in a retained project session.

`rbtree_size_propagate.click` checks the unchanged propagation callback for
its first visited leaf, whose parent is the exclusive stop. Both early break
and parent advance restore the leaf size to one and preserve its structural
links and tagged parent word. This covers a single iteration;
`rbtree_size_propagate_tree.click` below checks the full loop.

`rbtree_size_context.click` supplies the ancestor model for full propagation.
Each left or right frame retains its cached size, sibling subtree, and remaining
ancestors. Reconstruction preserves the erased tree shape, and the context depth
is nonnegative. The focused subtree count is bounded by the reconstructed whole
tree count, so the original whole-tree size bound also applies along the walk.
The early-stop theorem proves that replacing the focused subtree
with a valid subtree of the same cached size leaves all ancestor counts correct.
`rbtree_size_context_resources.click` owns both kinds of ancestor frame, including
metadata, links, sibling trees, and the remaining path. `certify_sized_context`
checks cached-count coherence while preserving these owned frames. Its recursive
reconstruction tactic restores a valid `sized_at` tree using unchanged ancestor
metadata when the focused cached size is unchanged. The path and result models
carry the reconstruction root, keeping the Linux callback signature unchanged.
`rbtree_size_walk.click` adds the checked ownership transitions used by that
loop: preparing bounded child counts, moving a repaired focus into its dirty
parent, rebuilding the path on early stop, and returning a certified whole
tree. Parent advance preserves reconstruction and decreases context depth.
`rbtree_size_propagate_tree.click` connects these helpers to the unchanged
arbitrary-length C loop. Its invariant retains the reconstruction root,
erased shape, and whole-tree size bound; context depth supplies termination.
The early break restores the remaining ancestors, and parent advance repairs
each visited node. At the exit join, checked disjunction projection exposes
that the cursor reached the stop or the walk is finished. The resource's active
case excludes the former, and its pending flag excludes the latter, so only
the finished case returns. The contract returns ownership of the whole valid
sized tree, preserving its root and erased shape and establishing recursive
count validity. `PropagateTree` and `sized_propagate_has_tree_contract` expose
the checked callable interface for callback-table integration.

This proves the recursive metadata invariant and its restoration through C
recomputation, rotation, and full ancestor propagation. Writable insertion
entry-point cases are described below; general ancestor and writable erase
integration remain unfinished.

This is an entry-point integration increment of
[chunk 14](../../issues/rbtree-example.md#augmented), not the completed
augmentation proof. The general structural entry-point proofs still import
callback contracts without writable footprints. The concrete sized insertion
cases below connect verified writable callbacks to selected paths. Each
imported module is verified separately; importing its contract does not rerun
its proof.

Run `click verify examples/rbtree-augmented` to check these entry points.

`rbtree_size_metadata.click` separates a checked sized subtree into ordinary
`rb_at` ownership and `sized_metadata_at` ownership of the cached size cells.
The metadata resource indexes its children by pure getters of its logical
model, rather than by the program's child links. `split_sized_tree` preserves
both the structural shape and the full sized model. This is the ownership
bridge for callbacks that update metadata while structural proofs rearrange
links; rejoining the resources and integrating the writable callback table
remain unfinished.

`rbtree_size_metadata.click` now verifies both directions of the ownership
bridge. `split_sized_tree` separates tree links from cache cells indexed by
logical node identities. `join_sized_tree` restores `sized_at` when the
structural shape agrees with the metadata model and its counts are valid.
It preserves the complete model and proves recursive termination by subtree
size. All nine split/rejoin expansion sites pass.

`rbtree_size_callback_frames.click` supplies `CopySizedStructure`: the unchanged
copy callback updates its two metadata cells while preserving independently
owned `rb_at` trees. Its execution theorem and expansion audit check the
returned structural ownership and models. `RotateSizedStructure` also certifies
that the unchanged rotation callback preserves an independently owned `rb_at`
tree at its new root while updating the source and target cache values. Its
proof exposes the existing guarded separation premises in all four child
null/non-null cases, then checks the call and returned frame. These are callback
frame contracts; writable callback-table integration with insertion and erasure
remains pending.

`rbtree_size_callbacks.click` connects the writable copy interface to the
concrete generated callback table. Its C translation unit combines the unchanged
compute, copy, rotation, and propagation bodies from the existing size examples;
no insertion or erasure body changes. `sized_callback_table` packages the proved
`PropagateTree`, `CopySizedStructure`, `RotateTreeLeft`, and `RotateTreeRight`
interfaces with stable views of the three fields. The concrete client constructs
that package from the execution theorems and lends it to the generic copy
dispatcher. The indirect call preserves both `rb_at` models and the source cache
while copying its value into the target cache. Propagation dispatch uses the same
package and returns the whole repaired sized tree, preserving its root and
erased shape and establishing recursive count validity through the previously
checked arbitrary ancestor loop. Rotation dispatch accepts a left or right dirty
subtree model, selects the corresponding proved callback interface inside the
borrowed table scope, and returns a recursively valid sized subtree. Both named
rotation interfaces preserve the structural shape and establish the repaired
root count. Connection to insertion and erasure remains to be checked.


`rbtree_size_insert.click` begins the writable-callback insertion boundary with
its no-parent case. It checks the unchanged `__rb_insert` body and both augmented
wrappers when the supplied node is the red root of a valid `sized_at` subtree.
The root becomes black; the exact cached sizes and child models are preserved.
The children may be nonempty. This path never invokes the rotation callback,
so it accepts any correctly typed callback without the plain insertion proof's
read-only `AugmentRotate` premise. `InsertSizedRoot` exposes the checked root-case
interface. This is not yet the ancestor or rotation paths of sized insertion,
and does not establish balancing from arbitrary child colors.

`rbtree_size_insert_black_parent.click` checks the other immediate insertion
exit and both wrappers: a red focus beneath a nonnull black parent. Its
`sized_black_parent_at` resource owns the sized subtree and ancestor tag;
the exact subtree model and full ancestor tag are preserved. It needs neither
root-field ownership nor a callback contract because this path reads neither
the root field nor calls the callback. The ancestor can be at any depth, but
this case stops immediately; color flips and general rotations remain pending.


`rbtree_size_insert_rotation.click` checks the unchanged `__rb_insert` body and
both augmented wrappers for a left-left three-node rotation at the root. The
input owns the black grandparent, red parent and red focus with valid cached
sizes 3, 2 and 1. After the structural rotation, the indirect callback is
checked against `RotateTreeRight`; it may write the promoted and demoted size
cells and returns a recursively valid `sized_at` tree. The result has a black
root and two red leaf children, with the exact expected structural model.
The wrappers accept the checked writable callback directly or through the
borrowed table field. This is the first insertion path that invokes a writable
metadata callback. Other rotation shapes, color flips, arbitrary ancestor
contexts and writable erase integration remain unfinished.


`rbtree_size_insert_mirrored_rotation.click` checks the mirrored right-right
three-node root case through the same three entry points, using
`RotateTreeLeft` for the writable callback. The returned model has the demoted
grandparent on the left and the inserted node on the right, with recursively
valid cached sizes. Both single-rotation directions are covered; the double-rotation boundary is
described below. Color flips and arbitrary ancestor contexts remain.

`rbtree_size_model_unique.click` proves that recursively valid cached counts
and an equal structural shape determine the entire `SizedTree` model. Its
structural induction matches the second model without adding another induction
hypothesis, and applies the original hypotheses to the two children. This
provides an exact model equality when a writable rotation callback returns a
repaired model whose shape is known.


`rbtree_size_insert_double_rotation.click` checks the left-right three-node
root insertion and both augmented insertion wrappers with writable callbacks.
The first left rotation repairs the parent/focus sizes; model uniqueness
identifies that returned subtree before the outer right rotation. The second
callback repairs the final root and demoted grandparent sizes. The result owns
the exact black-root/two-red-leaf shape with recursively valid subtree counts.
The Linux C is unchanged. Color flips, arbitrary ancestor contexts, and
writable erase integration remain unfinished.


`rbtree_size_insert_mirrored_double_rotation.click` checks the mirrored
right-left root case and both wrappers. It repairs the inner right rotation
before the outer left rotation, returning a black focus root with the
grandparent on the left and the original parent on the right. Both double
rotation directions now check two writable callbacks in sequence. Together
with the single rotations, all four three-node root rotation shapes are
covered with recursively valid cached sizes.

 `rbtree_size_insert_color_flip.click` and
`rbtree_size_insert_mirrored_color_flip.click` check the four-node color-flip
path in both orientations, including `__rb_insert` and both augmented
wrappers. The red parent and uncle become black, the focus moves to the
grandparent, and the loop continues before blackening that new root. The owned
`sized_context_at` chain has two ancestor frames before the flip and none
afterwards; its actual `sized_context_depth` supplies the decreasing measure.
All cached sizes and links are preserved, and the returned resource describes
the exact recolored sized tree. This path invokes no callback and accepts any
correctly typed rotation pointer. These are root-reaching flips; the
repeated-flip chain proof below handles arbitrary ancestor chains. Writable
erase integration remains unfinished.

 `rbtree_size_insert_context_color_flip.click` and its mirrored counterpart
prove a flip beneath a nonnull black parent with arbitrary owned children of
the red focus, symbolic cached sizes at the focus, parent, and grandparent,
and an arbitrary owned outer ancestor context with arbitrary sibling trees.
The parent's other child and both uncle children are arbitrary owned sized
subtrees. Cached parent and grandparent sizes remain symbolic, and count
obligations use shared equality closure without model-spelling rewrites. The
loop moves past the two inner frames, stops at the black parent, and uses the
previously proved `restore_sized_context` to return the whole root tree. The
postcondition states its exact model as the unchanged outer context filled
with the recolored subtree; cached counts and links are preserved throughout.
The ranking measure is the actual context depth, reduced by two on the
continuing path. This covers a single flip followed by a black-parent exit.
The repeated-flip chain proof below handles red outer ancestors.


`rbtree_size_change_child.click` now checks the insertion translation unit's
`__rb_change_child` helper using a file-qualified contract. It replaces a
root, left-parent, or right-parent incoming link while retaining the exact
owned `SizedContext`, every ancestor cache, the old focus cache, and the old
focus parent/color word. A nonempty sibling is separated using its existing
ownership. This supplies the sized incoming-link interface for non-root
rotations.


`rbtree_size_rotate_set_parents.click` also checks the selected insertion
helper for root, left-parent, and right-parent contexts. It transfers the old
packed parent/color word to the promoted node, sets the demoted node's new
parent/color word, and calls the checked sized incoming-link helper. The
ancestor model and caches and the demoted node's cache are preserved. Full
non-root insertion must still compose this helper with the writable rotation
callback and whole-context restoration.


`rbtree_size_link_distinct.click` proves the remaining parent-update separation
precondition from owned ancestor frames and the promoted node's word. It
handles root, left-parent, and right-parent contexts, preserves the exact link
model, and uses the shared indexed separation rule through `assumption()`.
The sized parent-update helper now calls this proof internally, so its callers
no longer need an explicit parent-disequality premise. Full non-root insertion
still needs the writable callback and whole-context restoration.


`rbtree_size_insert_context_rotation.click` composes the checked parent-update
helper and writable size callback for a left-left insertion rotation under an
arbitrary owned ancestor context. The unchanged C and both augmented insertion
wrappers return ownership of the whole root tree after refolding the repaired
three-node subtree through the preserved ancestor context. The postcondition
identifies its model with `sized_plug` and retains the subtree's exact rotated
shape. Its retained-session expansion is a nightly regression for call-frame
address matching. The other non-root rotation shapes remain.


`rbtree_size_insert_mirrored_context_rotation.click` proves the right-right case
with the same whole-root ownership result and unchanged ancestor caches. Both
augmented insertion wrappers check the mirrored writable callback. The two
context cases share the packed black-parent-word lemma in the parent-update
helper, and each has a retained expansion regression.

 `rbtree_size_insert_context_double_rotation.click` and its mirrored
counterpart check the left-right and right-left three-node insertion rotations
under an arbitrary owned ancestor context. Each composes two writable size
callbacks, identifies the intermediate repaired model by uniqueness, updates
the incoming link, and restores ownership of the whole root tree. The
postcondition relates that model to `sized_plug` of the original context and
repaired subtree. Both augmented insertion wrappers preserve the same result.
The repeated-flip chain proof below covers red outer ancestors; general
rotation subtrees and writable erase integration remain unfinished.


`rbtree_size_recolor.click` supplies shared model operations for root recoloring
and insertion color flips. Its explicit lemmas preserve cached values and
recursive count validity for arbitrary subtrees and identify their shapes with
the existing `rb_recolor` and `rb_insert_fix_recolor` operations. The root-only
insertion proof imports this shared recoloring definition.


`rbtree_size_insert_context_stop.click` checks the black-parent stopping case
for arbitrary focused and sibling subtrees and an arbitrary owned outer context.
Its input bundles the tree and path around their shared cached size. Either
parent orientation returns the root link and ownership of the whole root tree,
whose exact model is the original context filled with the original subtree.
Both augmented insertion wrappers preserve that result.

 `rbtree_size_insert_flips_model.click` defines a chain of pending insertion
color flips in all four ancestor orientations, ending at the root or an owned
black-parent boundary. It defines the resulting recolored tree and proves the
chain-depth bound and the context-parent relation. These definitions supply
the invariant and ranking measure for the repeated-flip C loop proof below.

`rbtree_size_insert_flips.click` bundles the current owned subtree and ancestor
path in `sized_flip_state`. Its checked `restore_sized_flip_state` tactic
returns the root link and the whole tree with the exact `sized_plug` model and
null root parent. The chain-to-context relationship is an explicit contract
premise, rather than an implicit promise of this general cursor resource.

`rbtree_size_insert_flip_boundary.click` proves both chain stopping cases using
that cursor: a root focus is colored black, and a focus beneath a black parent
returns without writes. Both ancestor orientations and the two augmented
insertion wrappers preserve the exact `sized_flip_result` model and cached
subtree sizes. These proofs accept arbitrary owned subtrees and outer contexts;
the chain proof below also checks the four continuing flip cases.


`rbtree_size_insert_flip_chain.click` checks arbitrarily many color-flip
iterations in the unchanged insertion C. Its chain may mix LL, LR, RL, and RR
ancestor orientations and ends at the root or a black-parent boundary. Focus,
sibling, and uncle subtrees and all valid cached counts remain symbolic. Each
iteration recolors the parent and uncle black, moves the red focus to the
grandparent, and decreases the chain depth. The entry and both augmented
wrappers return ownership of the whole root tree with the exact
`sized_flip_result` model and null root parent. No rotation callback is invoked
on these paths. This completes repeated flips; a general insertion contract
still needs arbitrary rotation subtrees and chains ending in a rotation.

`rbtree_size_insert_flips_order.click` proves that `sized_flip_result` preserves
the complete in-order sequence of the original plugged tree. Its induction
uses the checked recoloring and context-transport lemmas, so it covers every
chain length and orientation without a separate C execution proof.
