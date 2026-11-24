# Expansion keeps outcome closers out of pruned C branches

A branch excluded by the entry facts has no return value. Its sibling's
outcome proof must remain in the branch that returned.

```c filename=pruned.c
int32 f(int32 n) {
    if (n > 0) {
        return 5;
    }
    return 7;
}
```

```click
verifying "pruned.c";
int32 f(int32 n) {
    requires n == 5;
    ensures result == 5 or result == 7;
} by {
    branch { true => { step(); close(); } false => { step(); close(); } }
}
```

```expect
pass
```
