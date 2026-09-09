# By-value struct postconditions cannot expose a modified callee copy

```c filename=t.c
struct pair {
    int32 first;
    int32 second;
};

int32 bump(struct pair value) {
    value.first = 5;
    return value.first;
}

int32 call_bump() {
    struct pair original;
    int32 r;
    original.first = 4;
    original.second = 0;
    r = bump(original);
    return original.first;
}
```

```click
verifying "t.c";

int32 bump(struct pair value) {
    ensures value.first == 5;
} by {
    execute();
    simp();
}

int32 call_bump() {
    ensures result == 999;
} by {
    execute();
    simp();
}
```

```expect
fail: by-value aggregate parameter `value` is modified, but a postcondition reads its current state
```
