# Separate calls still have separate results

Two interfaces constrain each call, but do not promise determinism across calls.
The empty callback parameter list uses C0's `()` spelling of C's `(void)`.

```c filename=joint.c
int32 twice(int32 (*callback)()) {
    int32 first = callback();
    int32 second = callback();
    return first == second;
}
```

```click
contract int32 Lower() { ensures result >= 0; }
contract int32 Upper() { ensures result <= 1; }
verifying "joint.c";
int32 twice(int32 (*callback)()) {
    requires Lower(callback);
    requires Upper(callback);
    ensures result == 1;
} by { execute(); simp(); }
```

```expect
fail: unclosed goal
```
