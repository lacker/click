# explicit fact transport between simple statement steps

`step()` does not automatically move the entry fact to the post-store memory
snapshot. `transport(source, target)` invokes that one frame-transport rule
explicitly before the next statement uses the current fact.

```c filename=simple_statement_step_explicit_transport.c
int32 set_second_return_first(int32 p[2]) {
    p[1] = 9;
    return p[0];
}
```

```click
verifying "simple_statement_step_explicit_transport.c";

predicate first_is_seven(int32 p[]) {
    p[0] == 7
}

int32 set_second_return_first(int32 p[2]) {
    requires first_is_seven(p);
    consumes p[0..2];
    mutable p[1..2];

    produces p[0..2];
    ensures result == 7;
} by {
    unfold(first_is_seven);
    step();
    transport(old(p[0]) == 7, p[0] == 7);
    step();
    frame();
    simp();
}
```

```expect
pass
```
