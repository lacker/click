# Unknown proof marks are diagnosed directly

A bare `at(name, ...)` selector must refer to an earlier `mark name;` in the
same proof.

```c filename=proof_mark_unknown.c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "proof_mark_unknown.c";

int32 identity(int32 x) {
    ensures result == at(start, x) by {
        execute();
        simp();
    }
}
```

```expect
fail: unknown proof mark `start`
```
