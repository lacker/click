# Old reads of a by-value struct parameter remain valid

An entry-state read describes the caller's argument image and does not expose
the callee's private post-state copy.

```c filename=t.c
struct pair {
    int32 first;
};

int32 bump(struct pair value) {
    value.first = 5;
    return 0;
}
```

```click
verifying "t.c";

int32 bump(struct pair value) {
    ensures old(value.first) == old(value.first);
} by {
    execute();
    simp();
}
```

```expect
pass
```
