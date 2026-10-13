# `execute()` in a proof `if` arm names the failing alias case

The negative of
`mdtests/execute_in_a_proof_if_arm_splits_a_loads_alias_cases.md`. In the case
`v == 0` the read is the `9` stored through `buf[v]`, so the claim fails there
as an ordinary unclosed goal naming that case.

```c filename=execute_in_a_proof_if_arm_names_the_failing_alias_case.c
int32 f(int32 u, int32 v) {
    int32 r;
    int32* buf;
    buf = malloc(16);
    if (buf == 0) {
        return 0;
    }
    buf[0] = 3;
    buf[u] = 7;
    buf[v] = 9;
    r = buf[0];
    free(buf);
    return r;
}
```

```click
verifying "execute_in_a_proof_if_arm_names_the_failing_alias_case.c";

int32 f(int32 u, int32 v) {
    requires 0 <= u;
    requires u < 4;
    requires 0 <= v;
    requires v < 4;
    ensures result == 0 or result == 3;
} by {
    step();
    step();
    step();
    if buf == 0 {
        execute();
        simp();
    } else {
        step();
        step();
        step();
        step();
        execute();
        simp();
    }
}
```

```expect
fail: case: [<pointer A> != 0, 0 == v]
```
