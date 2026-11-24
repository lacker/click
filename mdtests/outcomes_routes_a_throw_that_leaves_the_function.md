# `outcomes` routes a throw that leaves the function

At a maybe-throwing call outside any `try`, `outcomes` splits the call's
two successors. The `threw` arm starts at the exceptional function exit.
The `returned` arm starts after the call and continues into the second call's
own nested `outcomes`.
Each arm proves the claims its paths owe.

```c filename=outcomes_routes_a_throw_that_leaves_the_function.c
int32 helper(int32 x) { return x; }
int32 caller(int32 x) {
    int32 y = helper(x);
    int32 z = helper(y);
    return z;
}
```

```click
verifying "outcomes_routes_a_throw_that_leaves_the_function.c";

int32 helper(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}

int32 caller(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
} by {
    step();
    outcomes {
        returned => {
            step();
            step();
            outcomes {
                returned => {
                    step();
                    step();
                    close();
                }
                threw => {
                    close();
                }
            }
        }
        threw => {
            close();
        }
    }
}
```

```expect
pass
```
