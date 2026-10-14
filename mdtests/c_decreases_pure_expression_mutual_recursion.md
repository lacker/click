# an expression recursion measure ranks a mutually recursive component

`even` calls `odd` and `odd` calls `even`. Each declares an expression
measure, and both measures have one shape: a single `int32` component. While
`even` is certified, its recursion anchor holds `level(n)` read at `even`'s
entry, and the call to `odd`, the other member of its recursive component,
owes `odd`'s own measure, read at the call, nonnegative and strictly below that
value, exactly as a self-call would. `odd` owes the same at its call to
`even`. Every call in the cycle descends in one order, so the cycle is finite.
[`c_decreases_mutual_recursion.md`](c_decreases_mutual_recursion.md) is the
same pair ranked by `decreases n`, whose analysis reads the bodies instead.

```c filename=c_decreases_pure_expression_mutual_recursion_even.c
int even(int n) {
    int result;
    if (n > 0) {
        result = odd(n - 1);
        return result;
    }
    return 1;
}
```

```c filename=c_decreases_pure_expression_mutual_recursion_odd.c
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
verifying "c_decreases_pure_expression_mutual_recursion_even.c";
verifying "c_decreases_pure_expression_mutual_recursion_odd.c";

function level(n: int32) -> int32 {
    n
}

int32 even(int32 n) {
    decreases level(n);
    requires n >= 0;
    ensures result >= 0;
} by {
    step();
    branch then {
        have 0 <= level(n - 1) by {
            unfold(level(n - 1));
            apply(int32_positive_predecessor_is_nonnegative(n)) using {
                n > 0;
            }
        }
        have level(n - 1) < level(n) by {
            unfold(level(n - 1));
            unfold(level(n));
            apply(int32_positive_predecessor_strictly_decreases(n)) using {
                n > 0;
            }
        }
        step();
        step();
        simp();
    } else {}
    step();
    simp();
}

int32 odd(int32 n) {
    decreases level(n);
    requires n >= 0;
    ensures result >= 0;
} by {
    step();
    branch then {
        have 0 <= level(n - 1) by {
            unfold(level(n - 1));
            apply(int32_positive_predecessor_is_nonnegative(n)) using {
                n > 0;
            }
        }
        have level(n - 1) < level(n) by {
            unfold(level(n - 1));
            unfold(level(n));
            apply(int32_positive_predecessor_strictly_decreases(n)) using {
                n > 0;
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
pass
```
