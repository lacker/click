# A pointer to a local that ended at one exit cannot be read after the loop

`stale` points `view` at `inner`, a local of the loop body, on one path and
leaves it at `kept` on the other. When that path breaks out, `inner`'s
lifetime ends, so after the loop `view` may designate storage that no longer
exists. The exits also differ in the record of automatic storage, which the
join reconciles by keeping every exit's tombstones
([`loop_break_exit_after_a_call_with_a_local_joins.md`](loop_break_exit_after_a_call_with_a_local_joins.md)).
Nothing about that grants access through `view`: the read after the loop is
refused.

```c filename=stale.c
int32 stale(int32 flag) {
    int32 kept = 0;
    int32* view = &kept;
    while (true) {
        if (flag == 0) {
            int32 inner = 5;
            view = &inner;
            break;
        }
        break;
    }
    return *view;
}
```

```click
verifying "stale.c";

int32 stale(int32 flag) {
    ensures result == 0 or result == 5;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases 0;

        maintain by {
            if flag == 0 {
                step();
                step();
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
fail: missing resource fact `views
```
