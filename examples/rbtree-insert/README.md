# Linux rbtree insertion frontier

This project uses the shared model from `../rbtree-model/rbtree_model.click`.
The Linux-derived C in `rbtree.h` and `rb_insert_color.c` is unchanged from the
former `mdtests/rb_insert_color.md` fixture.

`rbtree_insert.click` is the green project entry: it checks that the shared
model and unchanged C load together, but intentionally selects no insert
proof. `rbtree_insert.frontier` contains the full insert contract and current
proof attempt. The examples integration test selects that frontier separately
and requires its bounded diagnostic to remain at the first unfinished
black-uncle path (statement 42 of the loop body, `augment_rotate(gparent,
parent)`, with 9 `break`s and 4 `continue`s complete). A passing import-only
entry therefore does not represent the insert proof as complete.

The proof so far covers `initialize`, the root-blackening and black-parent
`break`s, and the uncle-red `continue` on all four frame combinations: each
recolours the uncle, the parent, and the grandparent, refolds the three nodes
at their new models, and closes the loop's nine invariants and the two-frame
structural descent through `ctx_insert_case1_left_step` or
`ctx_insert_case1_right_step` from the shared model.

Case 3 on the left-left frames with a black uncle is complete for six of its
eight leaves: the proof splits on the parent's other child (empty or a node,
since `if (tmp)` writes its parent word) and on the grandparent's own frame
(`Top`, `Left`, or `Right`, since `__rb_change_child` writes that frame's child
cell), steps through the rotation and the inline `__rb_rotate_set_parents`,
refolds the grandparent and the new frame at the rotated parent, and states
the three whole-tree facts the post-loop proof will read at the `break`
through `ctx_insert_case3_left_step`. The two unfinished leaves are the
`Right` grandparent frame whose other child is a node: that child has to be
unfolded to decide `parent->rb_left == old`, and it cannot yet be refolded,
because a fold at the pointer the proof arm bound does not find the cells the
unfold published under the loaded pointer's spelling. The other three frame
combinations, the empty-uncle leaves, the body's end, the post-loop proof, and
`rb_insert_color` remain.

Run the normal full rbtree scope with:

```sh
click verify examples/rbtree-model
click verify examples/rbtree-insert
```

Inspect the unfinished proof directly with:

```sh
click verify examples/rbtree-insert/rbtree_insert.frontier
click verify --trace-proof __rb_insert --trace-to LINE examples/rbtree-insert/rbtree_insert.frontier
```

The frontier imports the model from the sibling project, so its project root
is `examples`, the nearest directory holding both; `--trace-to` reaches the
tactics inside the fixup's proof `match` arms and its `preserve` body.
