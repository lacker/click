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
    branch then {
        have 0 <= m - 1 by {
            apply(int32_positive_predecessor_is_nonnegative(m)) using {
                m > 0;
            }
        }
        have m - 1 < m by {
            apply(int32_positive_predecessor_strictly_decreases(m)) using {
                m > 0;
            }
        }
        step();
        step();
        simp();
    } else {}
    step();
    simp();
}
```

```expect
fail: `n` is nonnegative at the recursive call
```
