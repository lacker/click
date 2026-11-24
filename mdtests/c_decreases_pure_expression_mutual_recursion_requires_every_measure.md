# every member of an expression-ranked component declares a measure

`odd` declares no measure, so a call from `even` to `odd` has no callee
measure to read, and the cycle would be ranked only on `even`'s side. The call
is refused by name.

```c filename=c_decreases_pure_expression_mutual_recursion_requires_every_measure_even.c
int even(int n) {
    int result;
    if (n > 0) {
        result = odd(n - 1);
        return result;
    }
    return 1;
}
```

```c filename=c_decreases_pure_expression_mutual_recursion_requires_every_measure_odd.c
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
verifying "c_decreases_pure_expression_mutual_recursion_requires_every_measure_even.c";
verifying "c_decreases_pure_expression_mutual_recursion_requires_every_measure_odd.c";

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
fail: `odd` is in `even`'s recursive component but declares no expression `decreases` measure
```
