# An `outcomes` threw arm refuses a false exceptional claim

The negative of `mdtests/outcomes_routes_a_throw_that_leaves_the_function.md`:
`helper` throws 7, so the threw arm cannot establish that `caller` throws 8.

```c filename=outcomes_threw_arm_refuses_a_false_exceptional_claim.c
int32 helper(int32 x) { return x; }
int32 caller(int32 x) {
    int32 y = helper(x);
    y = x;
    return y;
}
```

```click
verifying "outcomes_threw_arm_refuses_a_false_exceptional_claim.c";

int32 helper(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}

int32 caller(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 8;
} by {
    step();
    outcomes {
        returned => {
            step();
            step();
            step();
            close();
        }
        threw => {
            close();
        }
    }
}
```

```expect
fail: did not retain a complete proof for `caller.exceptional_ensures_0`
```
