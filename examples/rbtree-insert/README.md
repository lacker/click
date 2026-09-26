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

The frontier sidecar imports the model by a path above its own directory, and
`click verify` on a single sidecar takes that sidecar's directory as the
project root, so the file cannot be verified on its own from the command line
today. The examples integration test loads it with the `examples` root; to
iterate on it, copy it beside a copy of the model under one scratch root and
verify that directory.
