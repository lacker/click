# A one-past-the-end pointer is not compared with another object

C11 6.5.9p6: a pointer one past the end of one array object compares equal to
the start of a different object when the implementation places the second
directly after the first. The answer depends on object placement, which Click
does not model, so `(a + 2) != b` for two distinct complete objects is refused
rather than decided. Previously the distinct blocks decided it `1`.

```c filename=a_one_past_the_end_pointer_is_not_compared_with_another_object.c
int32 f(int32 x) { int32 a[2]; int32 b[2]; a[0] = 1; b[0] = 2; return (a + 2) != b; }
```

```click
verifying "a_one_past_the_end_pointer_is_not_compared_with_another_object.c";

int32 f(int32 x) {
    ensures result == 1;
} by { execute(); simp(); }
```

```expect
fail: one-past-the-end pointer with the start of another object: whether the two objects are adjacent is unspecified
  operation: `(a + 2) != b`
```
