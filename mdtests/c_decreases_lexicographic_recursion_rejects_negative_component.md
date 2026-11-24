# every component of a lexicographic recursion measure stays nonnegative

The call lowers the first component, so the tuple is lexicographically
smaller, but it passes `-1` as the second one. A lexicographic order is well
founded only on tuples of nonnegative components, so the call also owes `0 <=
n` for the value it passes, and that member is refused.

```c filename=c_decreases_lexicographic_recursion_negative.c
int32 walk(int32 m, int32 n) {
    int32 result;
    if (m > 0) {
        result = walk(m - 1, -1);
        return result;
    }
    return 0;
}
```

```click
verifying "c_decreases_lexicographic_recursion_negative.c";

int32 walk(int32 m, int32 n) {
    decreases (m, n);
    requires m >= 0;
    ensures result == 0;
} by {
    step();
    branch {
        true => {
            have 0 <= to_integer(m - 1);
            have to_integer(m - 1) < to_integer(m);
            step();
            step();
            close();
        }
        false => {}
    }
    step();
    close();
}
```

```expect
fail: `n` is nonnegative at the recursive call
```
