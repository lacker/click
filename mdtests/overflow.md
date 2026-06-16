# signed overflow is C undefined behavior

This checks that signed `int32` overflow is not treated as an ordinary wrapped
return value. The expected failure is useful: it confirms that `auto` reaches a
C undefined behavior outcome instead of proving the postcondition.

```c filename=overflow.c
int32 overflow() {
    return 2147483647 + 1;
}
```

```click
verifying "overflow.c";

int32 overflow() {
    ensures no_wrapping_result: result == 0 by auto;
}
```

```expect
fail: outcome was UndefinedBehavior(SignedOverflow)
```
