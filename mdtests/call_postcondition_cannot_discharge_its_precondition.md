# A callee's postcondition cannot discharge its entry requirement

The callee preserves its positive input. A caller with a nonpositive input
cannot apply that contract: its guarantee is conditional on the requirement,
so it must not be included in the context used to check that requirement.

```c filename=call.c
int32 callee(int32 x) { return x; }
int32 caller(int32 a) { return callee(a); }
```

```click
verifying "call.c";

int32 callee(int32 x) {
    requires x > 0;
    ensures x > 0;
    ensures result == x;
}

int32 caller(int32 a) {
    requires a <= 0;
    ensures result == a;
} by {
    step();
    step();
    close();
}
```

```expect
fail: unproved obligation: `a > 0`
```
