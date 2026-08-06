# count_to_three loop body is externally immutable

This checks that frontier-loop `immutable` permits stack-local loop updates while
still proving that the whole loop span does not mutate externally visible
memory.

```c filename=count_to_three_loop_immutable.c
int32 count_to_three_loop_immutable() {
    int32 i;
    i = 0;
    while (i < 3) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "count_to_three_loop_immutable.c";

int32 count_to_three_loop_immutable() {
    ensures returns_three: result == 3;
} by {
    step();
    step();
    loop {
        invariant i >= 0;
        invariant i <= 3;
        immutable by frame;
    }
    step();
    simp();
}
```

```expect
pass
```
