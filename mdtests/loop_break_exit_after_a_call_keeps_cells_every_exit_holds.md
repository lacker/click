# A fresh post-loop state keeps the cells every exit holds

The loop of
[`loop_break_exit_ordinary_join_keeps_post_loop_read.md`](loop_break_exit_ordinary_join_keeps_post_loop_read.md),
except that one exit calls `repaint`, which declares a local and, having no
Click contract, runs its body at the call site. The exits now
disagree on the record of automatic storage, so the successor's memory takes a
freshly minted identity with no recorded history
([`loop_break_exit_after_a_call_with_a_local_joins.md`](loop_break_exit_after_a_call_with_a_local_joins.md)).

The claim about `q[0]` still holds. The function owns `q[0..1]`, so every exit
holds the cell's value, and the join keeps every cell the exits agree on. What
the fresh identity gives up is narrower: a load after the loop of a cell some
exit does not hold is related to no load before or inside the loop, where an
unchanged identity could have related it through the memory's history.

```c filename=keep_call.c
static void repaint(int32* p) {
    int32 next = 0;
    p[0] = next;
}

int32 keep(int32* p, int32* q, int32 flag) {
    while (true) {
        if (flag == 0) {
            repaint(p);
            break;
        } else {
            p[0] = 0;
            break;
        }
    }
    return q[0];
}
```

```click
verifying "keep_call.c";

int32 keep(int32* p, int32* q, int32 flag) {
    owns p[0..1];
    owns q[0..1];
    ensures result == old(q[0]);
} by {
    have separate(memory(p[0]), memory(q[0]));
    loop {
        decreases 0;
        invariant q[0] == old(q[0]);
        owns p[0..1];

        preserve by {
            if flag == 0 {
                step();
                step();
                have q[0] == old(q[0]) by { known(); }
                step();
            } else {
                step();
                step();
                have q[0] == old(q[0]) by {
                    normalize() using {
                        old(q[0]) == old(q[0]);
                    };
                }
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
