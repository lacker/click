# Linux rbtree erase

`rbtree_erase.click` verifies the unchanged Linux `__rb_erase_augmented`
implementation when the erased node is the root and has at most one child.
It covers an empty replacement, a right child, and a left child. The contract
returns the erased node's raw field ownership and a whole `rb_root_at(root)`
whose root is black, whose parent is null, and whose in-order sequence is the
concatenation of the old left and right subtrees. The returned fixup parent is
null: these root cases need no subsequent erase fixup.

`rbtree_erase_successor.click` additionally verifies two-child root deletion
when the right child is a red leaf: the immediate-successor branch. It proves
the exact `rb_successor_splice` model, red-black validity, parent consistency,
and the old left/right in-order sequence, with a null fixup parent. Its
contract requires a parent-consistent input tree.

`rbtree_erase_black_successor.click` covers an immediate black-leaf successor
at the root. It returns the successor as a non-null fixup parent, an empty
hole, and the exact `ctx_at` context missing one black level. The context
preserves parent consistency and the remaining in-order sequence. This is
the input to erase-color fixup; it does not claim that the tree is already
red-black.

`rbtree_erase_child_successor.click` covers an immediate successor with a
nonempty replacement child at the root. Blackening the child's root restores
balance without erase-color fixup. The proof returns the exact remaining
model, red-black validity, parent consistency, and the remaining in-order
sequence, with a null fixup parent.

`rbtree_erase_black_leaf.click` covers a black leaf below the root, on either
parent link. It returns the detached node's fields, an empty hole, the unchanged
context model with a one-black-level deficit, and the non-null parent to fix up.
The right-child proof unfolds the sibling so execution can establish that the
left link does not alias the erased node. This sidecar holds and returns exclusive
ownership of the callback table; the root sidecars borrow it with explicit
separation requirements.

`rbtree_erase_red_leaf.click` covers a red leaf below the root on either parent
link. Its unchanged context accepts an empty black hole at the same black
height, so balance is preserved and the fixup return is null. It uses the same
exclusive callback-table contract as the black-leaf sidecar.

`rbtree_erase_right_child.click` and `rbtree_erase_left_child.click` cover
deletion with one nonempty child, for either child direction, either parent
link, and deletion of the root.
Neither contract assumes the erased node's or child's color.
Validity implies that copying the erased node's parent/color word blackens the
child. The proofs return that exact replacement model and the unchanged context,
with whole-tree red-black validity, parent consistency, preserved child in-order
contents, and a null fixup parent. Both borrow the read-only callback table.

`rbtree_erase_nonroot_successor.click` extends the immediate red-leaf successor
case below the root, on either parent link. It returns the exact successor
subtree and unchanged outer context, whole-tree balance, parent consistency,
and the old left/right in-order contents, with null fixup. The erased node's
color is not assumed. It holds and returns exclusive callback-table ownership.

`rbtree_erase_nonroot_black_successor.click` covers an immediate black-leaf
successor below the root, on either parent link. It returns that successor as
the non-null fixup parent and the exact context with a one-black-level deficit.
Plugging its empty hole equals the intended successor splice in the original
outer context. Parent consistency is preserved; balance still needs fixup.

`rbtree_erase_nonroot_child_successor.click` covers an immediate successor
with a nonempty replacement child below the root, on either parent link.
The exact replacement blackens that child and preserves the outer context.
The contract proves whole-tree balance, parent consistency, in-order contents,
and null fixup without assuming the erased node's, successor's, or child's color.

`rbtree_erase_spine.click` covers deletion at any tree position with a deeper
successor that is a red leaf or has a nonempty right child. Its terminating
descent loop retains the exact left-only path. Small opening and closing helper contracts
expose the splice link. The verified parent-link helper transfers the outer
context to the successor.
The replacement branches join with one owned replacement link and its exact
model, then share the path rebuild and terminating outer-context reconstruction.
The nonempty child is blackened; a red leaf needs no color repair. Both cases
return the exact successor transplant with red-black validity, parent
consistency, preserved in-order contents, detached-node ownership, and null
fixup. A shared model theorem connects the leaf and nonempty-child splices.

`rbtree_erase_black_spine.click` covers deletion at any tree position with a
deeper black-leaf successor. After splicing out the leaf, `graft_erase_spine` joins the retained
descent path to the transplanted successor's context. The contract returns an
empty hole, the exact deficit context, its red-black and parent-consistency
invariants, preserved in-order contents, detached-node ownership, and the
nonnull minimum parent where color repair must begin.

`rbtree_change_child.click` verifies the shared C parent-link replacement
helper for root, left-child, and right-child links. Its contract retargets an
owned context while preserving its exact model and the old node's tag. Holding
that tag separates the old node from a nonempty sibling. Three mutation checks
reject a missing update on each link. This supplies the context transfer needed
by deeper non-root deletion.

These are C increments of chunk 11 in
[the rbtree issue](../../issues/rbtree-example.md). Zero/one-child deletion and
all immediate and deeper-successor exits now verify at any tree position.
This completes chunk 11 across the sidecars; each contract states its coverage,
and the C file retains all branches. Erase-color repair is next, in chunks 12–13.

`rbtree_erase_color_red_left.click` starts chunk 12 on the unchanged pinned
`____rb_erase_color`. It covers an empty left child below a red parent whose
right sibling is a black leaf. The two color writes restore balance; the
contract returns the exact whole-root model, parent consistency, and unchanged
in-order contents. The proof terminates through the first iteration's `break`
and a decreasing context-reconstruction helper. Its 31 expansion-audit sites
pass. `rbtree_erase_color_root_left.click` covers the black-root exit with the
same empty left child and black leaf sibling. It preserves the black root,
recolors the sibling, and proves that the parent cursor becomes null before
leaving the loop. Its exact model has the same balance, parent-consistency,
and in-order guarantees; all 20 audit sites pass.

`rbtree_erase_color_flips.click` covers repeated color flips with either
orientation at every ancestor, including nonempty focus and sibling subtrees
on later iterations. Its selector admits black siblings with black children, propagates through black
parents, and stops at a red parent or the root. Every continuing iteration
consumes a strict child of the context resource, which proves termination.
The result function specifies the exact whole-tree model; balance, parent
consistency, and in-order contents follow across the entire loop. All 39
expansion-audit sites pass. Mutations reject either missing cursor assignment,
missing parent blackening, and incorrect sibling recoloring. Rotations remain
outside that sidecar's selector.

`rbtree_erase_color_flips_outer.click` extends repeated propagation with a
terminal case-4 rotation in either direction. It admits a nonempty black focus
after propagation, a near subtree of either color, and arbitrary children of
the red far node. The same contract also covers red-parent and root exits.
Every continuing edge decreases the context, and the result specifies the
exact balanced, parent-consistent whole tree with unchanged in-order contents.
All 21 proofs and 168 expansion-audit sites pass. Eight mutation checks reject
broken cursor ascent, parent blackening, sibling recoloring, either parent
child link, far-child blackening, and near-child reparenting.

`rbtree_erase_color_flips_rotations.click` adds terminal cases 3 and 4 in both
directions after repeated propagation. It covers all black-sibling cases,
including nonempty focus, far, and inner-grandchild subtrees. The first rotation
reparents one grandchild under the old sibling; the second reparents the other
under the old parent. The contract retains the exact balanced, parent-consistent
whole-tree result and unchanged in-order contents. All 31 proofs and 300
expansion-audit sites pass. Eight
additional mutation checks reject broken inner links, the first grandchild's
parent/color write, and the two cursor assignments between rotations.

`rbtree_erase_color_flips_red_exit.click` adds red-sibling cases 1 and 2 after
propagation, in either direction. The deficit focus, the old sibling's opaque
far subtree, and both children of its near node may be nonempty. The first
rotation reparents the near node and retains the far subtree; the subsequent
color flip blackens the red parent and completes the repair. The exact result
remains balanced and parent-consistent with unchanged in-order contents, and
every continuing iteration decreases the context. All 33 proofs, 362
expansion-audit sites, and eight rotation-link, parent/color, and cursor mutation
checks pass.

`rbtree_erase_color_flips_red_outer.click` adds red-sibling cases 1 and 4
after propagation in either direction. The deficit focus, the old sibling's
far subtree, the new sibling's near subtree, and both children of its red far
node may be nonempty. The two rotations preserve the exact whole-tree result,
red-black balance, parent consistency, and in-order contents. Continuing loop
iterations still decrease the context. Red-sibling cases 1/3/4 after propagation
remain.

The color-flip-only sidecar has 1,091 lines, against the pinned function's 182 lines
including its remaining rotations. On this development build it profiles at
about 25 seconds (43 sidecar lines/second), down from 33 seconds after avoiding
redundant constructor refutations. No simple-step tail exceeds 500 ms; about
11 seconds remain in loop-control work. This is still below the project's
verification-speed target.

`rbtree_rotate_set_parents.click` verifies the rotation helper's incoming-link
replacement at the root or either parent link. It copies the original packed
word to the new root, reparents and recolors the old root, and preserves the
exact outer context. All 35 expansion-audit sites pass. This supplies the
shared parent-update step for the remaining rotations.

`rbtree_set_parent.click` verifies the parent update for a nonempty subtree
of either color, preserving both child models. All 11 audit sites pass;
two mutations reject a lost color bit and an incorrect parent.

`rbtree_erase_color_outer_left.click` and `rbtree_erase_color_outer_right.click`
verify the mirrored case-4 rotations for an empty deficit, an empty near child,
and a red far leaf. The parent may have either color under any outer context.
The unchanged C rotates the links, blackens the old parent and far child, and
gives the sibling the old parent's color. Both contracts return the exact
balanced root, consistent parent links, and unchanged in-order contents.
Both expansion audits pass all 97 sites. Eight mutation checks reject incorrect
parent/sibling child links and missing old-parent or far-child blackening.
`rbtree_erase_color_outer_nonempty_left.click` and its mirrored right sidecar
cover the nonempty near-child case. The near subtree is reparented with its
color and children preserved; both proofs return the exact balanced root,
consistent parent links, and unchanged inorder contents. Each passes all
111 audit sites. Four mutations reject a wrong near-child parent or attachment.
`rbtree_erase_color_inner_left.click` and its mirrored right sidecar cover
cases 3 and 4 for an empty deficit, a black sibling with a red inner leaf,
and an empty far child. Either parent color and arbitrary outer contexts are
supported. The two rotations return the exact balanced root, consistent
parent links, and unchanged in-order contents. Each passes all 95 expansion-audit
sites. Six mutations reject an incorrect inner-child detachment, old-sibling
attachment, or old-sibling parent.

`rbtree_erase_color_red_sibling_left.click` and its mirrored right sidecar
cover cases 1 and 2 for an empty deficit, a red sibling, and a black near leaf.
The parent is black and may sit under any outer context. The far subtree stays
folded throughout the rotation and color flip. Both proofs return the exact
balanced root, consistent parents, and unchanged in-order contents. Each passes
all 104 expansion-audit sites; six mutations reject either missing child-link
update or incorrect parent recoloring in the first rotation.
`rbtree_erase_color_red_sibling_outer_left.click` and its mirrored right sidecar
cover cases 1 and 4: the red sibling's black near child has an empty near child
and a red far leaf. Both rotations retain the original opaque far subtree and
return the exact balanced root, consistent parents, and unchanged in-order
contents under any outer context. Each passes all 121 expansion-audit sites.
Six mutations reject incorrect first- or second-rotation parent links and an
incorrect far-child parent.
`rbtree_erase_color_red_sibling_inner_left.click` and its mirrored right sidecar
cover cases 1, 3, and 4: the red sibling's black near child has a red inner leaf
and an empty far child. The three rotations preserve the original opaque far
subtree and return the exact balanced root, consistent parents, and unchanged
in-order contents under any outer context. Each passes all 127 expansion-audit
sites. Six mutations reject incorrect inner-child detachment, old-sibling
attachment, or old-sibling parent updates.
`rbtree_erase_color_red_sibling_outer_nonempty_left.click` and its mirrored
right sidecar cover cases 1 and 4 with a nonempty near subtree after the first
rotation. The parent-update helper preserves that subtree's color and children;
the two rotations retain the opaque outer far subtree. Both proofs return the
exact balanced root, consistent parents, and unchanged in-order contents under
any outer context. Each passes all 136 audit sites; four mutations reject an
incorrect near-child parent or attachment. Rotations after deficit propagation
and the complete `rb_erase` wrapper remain.

`rbtree_erase_color_flips_red_inner_right.click` extends the propagated repair
proof with red-sibling cases 1, 3, and 4 when the deficit is the right child.
The focus and rotation subtrees may be nonempty. It retains the existing
color-flip propagation and both orientations of cases 1/2 and 1/4, and returns
the exact balanced tree with consistent parents and preserved in-order contents.
The parent/color frame is explicit across the inner and outer updates, and the
saved child pointer is connected to the right link before the subtree is folded.
The mirrored propagated red-sibling inner rotation and complete erase wrapper
remain.

`rbtree_erase_color_flips_red_all.click` adds the mirrored left-deficit
red-sibling cases 1/3/4. It covers color-flip propagation followed by cases
1/2, 1/4, or 1/3/4, as well as the black-sibling rotations, in both directions
with nonempty focus and rotation subtrees. The exact result, parent links,
red-black invariants, and in-order contents are preserved. A structural context
proof derives case coverage from the black-deficit invariant, so callers need
no separate `erase_flips_red_all` precondition.

The same sidecar now verifies the unchanged `rb_erase` wrapper end to end for
all leaf deletions: red or black leaves on either parent link, and the sole
root. The splice borrows the callback table read-only and calls the verified
parent-link helper. For a nonroot black leaf, its empty hole and deficit
context satisfy the general repair contract; otherwise the wrapper refolds
the already balanced tree without calling repair.
The wrapper returns ownership of the detached node and a balanced root with
consistent parents and exactly the in-order contents of the old context with
the erased leaf removed. Its contract requires views of the static const dummy
callback fields; initialization of these views at program startup is outside
this local proof.

`rbtree_erase_left_child.click` and `rbtree_erase_right_child.click` also verify
the unchanged wrapper end to end when the erased node has exactly one child,
at the root or on either parent link. Their splice proofs borrow the constant
callback table without additional separation preconditions. They return the
detached node and a balanced, parent-consistent root with exact in-order
contents. Checked execution proves the repair call unreachable in these cases.
Two-child deletion still needs wrapper integration.

`rb_erase.c` includes the existing unchanged splice and repair extracts and adds
the dummy callbacks, const table, and `rb_erase` definition verbatim from pinned
`lib/rbtree.c`. All helper bodies and callback refinements are checked in this
combined sidecar.

The callback contracts describe the non-augmented case: callbacks cannot
mutate tree fields or require augmentation metadata. The borrowed table is
separated from fields the C may write. Metadata-carrying callbacks remain
chunk 14.

The input is extracted from `include/linux/rbtree_augmented.h` inside
[`input-closure.tar.gz`](../../integrations/linux-rbtree/input-closure.tar.gz).
The `rb_augment_callbacks` declaration and `__rb_erase_augmented` definition,
including comments, are verbatim. The header shim reuses the insertion
example's supported rbtree types and macros and spells the pinned
`__rb_parent` mask. This is not yet the complete pinned translation-unit
integration planned in chunks 21–24. The source is GPL-2.0-or-later.

The full erase project runs in the nightly example suite. Run `click verify examples/rbtree-erase` and
`click verify examples/rbtree-model`. The latter checks the imported pure
root-deletion and successor-splice theorems independently. Example regressions
pin the source and reject skipped parent/color writes, root replacement, or
the successor's left-child parent update. The successor's explicit final
claim closers also re-verify. Black-successor mutations reject a skipped root
replacement and incorrectly returning null instead of the fixup parent.

Replacement-child mutations reject a missing parent/color write and a write
that leaves the child red.

Non-root leaf mutations reject an unchanged left or right parent link, a null
fixup return for black leaves, and a non-null fixup return for red leaves.

One-child mutations reject unchanged parent links, missing parent/color writes,
leaving the replacement red, and a non-null fixup return.

Non-root red-successor mutations reject unchanged parent links, missing left
subtree attachment or parent updates, missing successor parent/color writes,
and a non-null fixup return.

Non-root black-successor mutations additionally reject null fixup and incorrectly
returning the erased node's parent instead of the successor.

Non-root replacement-child mutations also reject a missing child parent/color
write and a write that leaves the child red.

The shared `rbtree_spine_model.click` and `rbtree_spine_resources.click`
modules define the left-only descent path. Its anchor owns only the original
right child's left link, leaving that child's parent/color and right link
available for transplant. The terminating `refold_erase_spine` tactic rebuilds
a balanced subtree; `graft_erase_spine` instead keeps an empty deficit hole and
joins the path to its new outer context. Both preserve exact models.

The spine lemmas connect minimum identity, minimum parent, and minimum context
to the original subtree, commute minimum removal with path reconstruction, and
recover each frame's parent link from whole-tree parent consistency. The two
C sidecars use these shared lemmas after the unchanged descent loop.

Deeper-successor mutation checks reject missing splice and attachment writes,
wrong replacement parents or colors, spurious red-leaf fixup, and missing or
misdirected black-leaf fixup. The pinned-source check remains in the ordinary
gate; slow mutation checks run nightly.
