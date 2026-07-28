# C `if` statements do not require padding branches

This exercises realistic source syntax through the complete C0 and Click
pipeline: comments, a scalar declaration initializer, and an `if` without an
invented `else` statement.

```c filename=choose_nonnegative.c
int32 choose_nonnegative(int32 x) {
    // Declaration initializers preserve ordinary source order.
    int32 result = 0;
    if (x < 0) {
        result = 1;
    }
    return result;
}
```

```click
verifying "choose_nonnegative.c";

int32 choose_nonnegative(int32 x) {
    ensures result >= 0;
}
```

```expect
pass
```
