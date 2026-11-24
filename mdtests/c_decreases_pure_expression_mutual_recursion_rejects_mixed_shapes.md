# the members of an expression-ranked component share one measure shape

A call to a peer compares the peer's measure with the caller's entry reading,
component by component, so the two tuples must have one length. `odd`'s
measure has two components and `even`'s one, and the call is refused.

```c filename=c_decreases_pure_expression_mutual_recursion_rejects_mixed_shapes_even.c
int even(int n) {
    int result;
    if (n > 0) {
        result = odd(n - 1);
        return result;
    }
    return 1;
}
```

```c filename=c_decreases_pure_expression_mutual_recursion_rejects_mixed_shapes_odd.c
int odd(int n) {
    int result;
    if (n > 0) {
        result = even(n - 1);
        return result;
    }
    return 0;
}
```

```click
verifying "c_decreases_pure_expression_mutual_recursion_rejects_mixed_shapes_even.c";
verifying "c_decreases_pure_expression_mutual_recursion_rejects_mixed_shapes_odd.c";

function level(n: int32) -> int32 {
    n
}

int32 even(int32 n) {
    decreases level(n);
    requires n >= 0;
    ensures result >= 0;
} by {
    step();
    branch {
        true => {
            have 0 <= level(n - 1) by {
                unfold(level(n - 1));
                have 0 <= n - 1;
                close();
            }
            have level(n - 1) < level(n) by {
                unfold(level(n - 1));
                unfold(level(n));
                have n - 1 < n;
                close();
            }
            step();
            step();
            close();
        }
        false => {}
    }
    step();
    close();
}

int32 odd(int32 n) {
    decreases (level(n), level(n));
    requires n >= 0;
    ensures result >= 0;
} by {
    step();
    branch {
        true => {
            have 0 <= level(n - 1) by {
                unfold(level(n - 1));
                have 0 <= n - 1;
            }
            have level(n - 1) < level(n) by {
                unfold(level(n - 1));
                unfold(level(n));
                have n - 1 < n;
            }
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
fail: the members of a recursive component must declare measures of one shape
```
