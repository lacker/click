# a callback that shadows a function name is still a callback

The parameter `helper` hides the file-scope `helper` (C11 6.2.1p4), so
`helper(1)` calls whatever pointer the caller passed. `caller(0)` passes
`&spin`, which recurses on the same argument and never returns.

Both `decreases` clauses were certified anyway: the call lowered under the
shadowed function's own name, and the termination call graph resolves callees
by name, so it saw a call to the terminating file-scope `helper`. Naming the
parameter anything else was already rejected, which is the treatment an
indirect call gets.

```c filename=termination_shadowed_callback_rejected.c
int32 helper(int32 x) {
    return 1;
}

int32 spin(int32 x) {
    if (x > 0) {
        return spin(x);
    }
    return 1;
}

int32 f(int32 (*helper)(int32), int32 n) {
    if (n > 0) {
        return f(helper, n - 1);
    }
    return helper(1);
}

int32 caller(int32 n) {
    if (n > 0) {
        return caller(n - 1);
    }
    return f(&spin, 0);
}
```

```click
verifying "termination_shadowed_callback_rejected.c";

contract int32 One(int32 x) {
    ensures result == 1;
}

int32 helper(int32 x) {
    ensures result == 1;
}

int32 spin(int32 x) {
    ensures result == 1;
}

int32 f(int32 (*helper)(int32), int32 n) {
    decreases n;
    requires One(helper);
    ensures result == 1;
}

int32 caller(int32 n) {
    decreases n;
    ensures result == 1;
}
```

```expect
fail: every reachable loop, recursive cycle, and callee must have a checked ranking proof
```
