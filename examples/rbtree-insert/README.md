# Linux rbtree insertion

This project uses the shared model from `../rbtree-model/rbtree_model.click`.
The Linux-derived C in `rbtree.h` and `rb_insert_color.c` is unchanged from the
former `mdtests/rb_insert_color.md` fixture; `tests/examples.rs` pins both
files by SHA-256. The function bodies in `rb_insert_color.c` are copied from
Linux v6.8.12, but `rbtree.h` is a hand-written stand-in for the kernel
headers that differs from them; see
[Current rbtree status](../../docs/internals/roadmap.md#current-rbtree-status).

`rbtree_insert.click` proves the Linux insert fixup, `__rb_insert`, end to end.
It takes the context and the red subtree at the inserted node
(`ctx_at(node, root)` and `rb_at(node)`, with the frame-level red-black,
order, and parent-link facts the case theorems use) and produces the whole
fixed-up tree at the root as `rb_root_at(root)`: ownership of
`root->rb_node` and the `rb_at` tree it points to, whose model is red-black
with a black root, has the entry's in-order sequence, and has consistent
parent links.

The fixup stops wherever its rotation or recolouring finishes, with an
arbitrary number of context frames above that point. Folding them back into
one subtree at the root takes one `fold` per frame, which no finite script can
write, and the C has no loop that climbs back up. The user-defined tactic
`refold_to_root` does it instead. It folds one frame and applies itself to the
context above, ranked by `decreases ctx_depth(c.model)`, so a single
application turns any context and focus subtree into the whole tree at the
root, with `whole.model == plug(c.model, t.model)`. It needs only that the
plugged tree is parent-consistent, which every exit of the fixup loop
establishes.

The proof covers `initialize`, the root-blackening and black-parent `break`s,
the uncle-red `continue` on all four frame combinations, and all 96 rotation
`break`s: case 3 on the outer frames and case 2 then case 3 on the inner
ones, split on the uncle, the rotated nodes' children, and the
great-grandparent's frame. Every `break` states the three whole-tree facts
about `plug(c.model, t.model)`, so they survive the loop's exit join, and the
post-loop proof applies `refold_to_root` once and carries those facts to the
tree at the root.

`rb_insert_color`, the exported entry point, is proved too. It calls
`__rb_insert`, a `static __always_inline` helper, with the no-op
`dummy_rotate` as its augment callback. The helper has a verified contract,
so the call applies that contract like any call, and the proof is one call
step that hands the context and red subtree to `__rb_insert`'s binders and
takes back `rb_root_at(root)`. It states the same three whole-tree facts.

`tests/examples.rs` also checks that the proof refuses a copy of the C whose
root case skips `rb_set_parent_color(node, NULL, RB_BLACK)`.

Run it with:

```sh
click verify examples/rbtree-model
click verify examples/rbtree-insert
```

The sidecar imports the model from the sibling project, so its project root is
`examples`, the nearest directory holding both. `--trace-to` reaches the
tactics inside the fixup's proof `match` arms and its `preserve` body:

```sh
click verify --trace-proof __rb_insert --trace-to LINE examples/rbtree-insert/rbtree_insert.click
```
