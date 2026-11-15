# An exit that called a function with a local joins one that did not

`paint` leaves its `while (true)` by a `break` on both paths, and both paths
leave `p->shade` holding 0. One path stores the 0 itself; the other calls
`repaint`, which declares a local. `repaint` has no Click contract, so its body
runs at the call site, on `paint`'s own memory.

The two exits hold the same cells and own the same resources. They differ in
what the path recorded about automatic storage: the calling path's memory
holds a tombstone for `repaint`'s ended `next` and the forget mark that
retiring its cell left, and the calling path has taken one identity from the
counter that names re-entered declarations. The join reconciles each:

- the successor holds the union of the exits' tombstones;
- its counter is the largest of theirs, so no ended block's identity is
  issued again;
- its memory keeps the cells every exit holds and takes a freshly minted
  state identity, with no recorded history, so a later load of a cell it
  does not hold is related to no earlier load.

The unchanged Linux `__rb_insert` needs this: its rotation exits call
`__rb_rotate_set_parents`, which declares `parent`, and its early exits do
not. What the fresh identity gives up is pinned by
[`loop_break_exit_after_a_call_keeps_cells_every_exit_holds.md`](loop_break_exit_after_a_call_keeps_cells_every_exit_holds.md);
a loop whose exits agree keeps its memory's identity
([`loop_break_exit_ordinary_join_keeps_post_loop_read.md`](loop_break_exit_ordinary_join_keeps_post_loop_read.md)).

```c filename=paint_through_helper.c
struct node { int32 shade; };

static void repaint(struct node* p) {
    int32 next = 0;
    p->shade = next;
}

void paint(struct node* p, int32 flag) {
    while (true) {
        if (flag == 0) {
            repaint(p);
            break;
        } else {
            p->shade = 0;
            break;
        }
    }
}
```

```click
verifying "paint_through_helper.c";

void paint(struct node* p, int32 flag) {
    owns p->shade;
    ensures p->shade == 0;
} by {
    loop {
        decreases 0;
        owns p->shade;

        preserve by {
            if flag == 0 {
                step();
                step();
                step();
            } else {
                step();
                step();
                step();
            }
        }
    }
    step();
    solve();
}
```

```expect
pass
```
