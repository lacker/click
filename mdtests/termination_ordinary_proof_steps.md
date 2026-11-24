# Program termination uses ordinary goals and checked proof steps

A nested `have` proves the callee's return promise. Its caller uses that
promise directly, without reopening the callee's descent proof. The remaining
program goals close with `known`.

```c filename=termination_ordinary.c
int32 leaf(void) { return 7; }
int32 caller(void) { return leaf(); }
```

```click
verifying "termination_ordinary.c";
int32 leaf() { ensures result == 7; }
int32 caller() { ensures result == 7; }

termination by {
    have termination_returns("leaf") by {
        check_termination_local("leaf");
        check_termination_component("leaf", strict);
        check_termination_component("leaf", normal);
        close();
    }
    check_termination_local("caller");
    check_termination_component("caller", normal);
    check_termination_callbacks();
    close();
}
```

```expect
pass
```
