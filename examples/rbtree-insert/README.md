# Linux rbtree insertion frontier

This project uses the shared model from `../rbtree-model/rbtree_model.click`.
The Linux-derived C in `rbtree.h` and `rb_insert_color.c` is unchanged from the
former `mdtests/rb_insert_color.md` fixture.

`rbtree_insert.click` is the green project entry: it checks that the shared
model and unchanged C load together, but intentionally selects no insert
proof. `rbtree_insert.frontier` contains the full insert contract and current
proof attempt. The examples integration test selects that frontier separately
and requires its bounded diagnostic to remain at statement 23. A passing
import-only entry therefore does not represent the insert proof as complete.

Run the normal full rbtree scope with:

```sh
click verify examples/rbtree-model
click verify examples/rbtree-insert
```

Inspect the unfinished proof directly with:

```sh
click verify examples/rbtree-insert/rbtree_insert.frontier
```
