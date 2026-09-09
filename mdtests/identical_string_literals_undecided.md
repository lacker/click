# Identical C string literals must not be assumed distinct

The implementation may merge identical string literals, so pointer equality
between two occurrences cannot decide either way.

```c filename=identical_string_literals_undecided.c
int32 identical_string_literals_undecided() {
    uint8* first = "ok";
    uint8* second = "ok";
    if (first == second) {
        return 1;
    }
    return 0;
}
```

```click
verifying "identical_string_literals_undecided.c";

int32 identical_string_literals_undecided() {
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: unclosed goal
```
