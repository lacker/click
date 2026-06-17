# count_to_three loop body is externally immutable

This checks that loop-level `immutable` permits stack-local loop updates while
still proving that one loop body step does not mutate externally visible memory.

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
    loop 0 {
        invariant i >= 0 by auto;
        invariant i <= 3 by auto;
        immutable by frame;
    }
    ensures returns_three: result == 3 by auto;
}
```

```expect
pass
```
