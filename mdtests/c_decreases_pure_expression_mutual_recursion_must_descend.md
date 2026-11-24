# a call between mutually recursive functions owes descent

`odd` calls `even` with its own `n`, so `even`'s measure at the call equals
`odd`'s entry reading. The call is to a peer rather than to `odd` itself, and
it owes the same strict descent a self-call owes; nothing establishes it.

```c filename=c_decreases_pure_expression_mutual_recursion_must_descend_even.c
int even(int n) {
    int result;
    if (n > 0) {
        result = odd(n - 1);
        return result;
    }
    return 1;
}
```

```c filename=c_decreases_pure_expression_mutual_recursion_must_descend_odd.c
int odd(int n) {
    int result;
    if (n > 0) {
        result = even(n);
        return result;
    }
    return 0;
}
```

```click
verifying "c_decreases_pure_expression_mutual_recursion_must_descend_even.c";
verifying "c_decreases_pure_expression_mutual_recursion_must_descend_odd.c";

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
            step();
            close();
        }
        false => {}
    }
    step();
    close();
}

int32 odd(int32 n) {
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
fail: unproved obligation: `level(n) < level(n)`
```
