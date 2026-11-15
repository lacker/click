# explicit fact transport between simple statement steps

A fact about a cell the context proves unwritten keeps its meaning across a
step, so `p[0] == 7` already holds after the store to `p[1]`, and the proof
verifies without the `transport`. `transport(source, target)` states that one
frame-transport rule explicitly: it carries the entry fact `old(p[0]) == 7` to
the post-store state as `p[0] == 7` before the next statement uses it.

```c filename=simple_statement_step_explicit_transport.c
int32 set_second_return_first(int32 p[2]) {
    p[1] = 9;
    return p[0];
}
```

```click
verifying "simple_statement_step_explicit_transport.c";

predicate first_is_seven(p: int32[]) {
    p[0] == 7
}

int32 set_second_return_first(int32 p[2]) {
    requires first_is_seven(p);
    owns p[0..2];

    ensures result == 7;
} by {
    unfold(first_is_seven);
    step();
    transport(old(p[0]) == 7, p[0] == 7);
    step();
    solve();
}
```

```expect
pass
```
