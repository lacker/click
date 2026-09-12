# Loop exits that reach different states have no common successor

A loop statement has one successor, so the exits joined into it must stand at
one state. The guard-false exit stands at the loop's own exit state, where
every local the body writes is abstract. This `break` leaves after assigning
`i`, so the two exits reach different states and the rule refuses, naming the
component that differs rather than picking one state for both or dropping the
`break` path.

What is missing is a way to describe the state a loop exits in, the way
`branch ensuring` describes the state two arms join in. Until there is one, a
`break` is certified where it changes nothing the loop abstracts: see
[`loop_body_break_exit.md`](loop_body_break_exit.md).

```c filename=assign_then_break.c
int32 assign_then_break(int32 n) {
    int32 i = n;

    while (i > 0) {
        i = 1;
        break;
    }
    return i;
}
```

```click
verifying "assign_then_break.c";

int32 assign_then_break(int32 n) {
    requires n >= 0;
    ensures result >= 0;
} by {
    step();
    step();
    loop {
        invariant i >= 0;

        initialize by simp;
        preserve by {
            step();
            step();
        }
    }
    step();
    simp();
}
```

```expect
fail: loop exits reach different states
```
