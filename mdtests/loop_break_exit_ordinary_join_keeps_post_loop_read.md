# A loop whose exits agree keeps its read equalities

`keep` reads `q[0]` after a loop that never touches `q`, and claims the value
is what `q[0]` held at entry. The loop's two `break` exits differ only in the
value they store in `p[0]`, which the join abstracts. They agree on the
record of automatic storage, so the join keeps the first exit's memory and its
identity, and the read after the loop is related to the entry read exactly as
before. Compare
[`loop_break_exit_after_a_call_with_a_local_joins.md`](loop_break_exit_after_a_call_with_a_local_joins.md),
where the exits disagree on that record and the successor's memory takes a
fresh identity.

```c filename=keep_plain.c
static void repaint(int32* p) {
    int32 next = 0;
    p[0] = next;
}

int32 keep(int32* p, int32* q, int32 flag) {
    while (true) {
        if (flag == 0) {
            p[0] = 0;
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
verifying "keep_plain.c";

void repaint(int32* p) {
    owns p[0..1];
    ensures p[0] == 0;
}

int32 keep(int32* p, int32* q, int32 flag) {
    owns p[0..1];
    owns q[0..1];
    ensures result == old(q[0]);
} by {
    loop {
        decreases 0;
        owns p[0..1];

        maintain by {
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
    close();
}
```

```expect
pass
```
