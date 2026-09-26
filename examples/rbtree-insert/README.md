# Linux rbtree insertion frontier

This project uses the shared model from `../rbtree-model/rbtree_model.click`.
The Linux-derived C in `rbtree.h` and `rb_insert_color.c` is unchanged from the
former `mdtests/rb_insert_color.md` fixture.

`rbtree_insert.click` is the green project entry: it checks that the shared
model and unchanged C load together, but intentionally selects no insert
proof. `rbtree_insert.frontier` contains the full insert contract and current
proof attempt. The examples integration test selects that frontier separately
and requires its bounded diagnostic to remain at the first black-uncle path
(statement 22 of the loop body, `tmp = parent->rb_right`). A passing
import-only entry therefore does not represent the insert proof as complete.

The proof so far covers `initialize`, the root-blackening and black-parent
`break`s, and the uncle-red `continue` on all four frame combinations: each
recolours the uncle, the parent, and the grandparent, refolds the three nodes
at their new models, and closes the loop's nine invariants and the two-frame
structural descent through `ctx_insert_case1_left_step` or
`ctx_insert_case1_right_step` from the shared model. The uncle-black rotation
`break`s, the body's end, the post-loop proof, and `rb_insert_color` remain.

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
