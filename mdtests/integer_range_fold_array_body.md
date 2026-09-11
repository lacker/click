# Integer range folds retain a checked array body

This is the smallest source-level memory smoke for a fold body.  The range is
fixed so the append law has one concrete item, while the body still captures a
pointer read from a required immutable segment.

```c filename=integer_range_fold_array_body.c
int32 array_fold_append_at_zero(int32 a[]) {
    return 0;
}
```

```click
verifying "integer_range_fold_array_body.c";

int32 array_fold_append_at_zero(int32 a[]) {
    requires loadable(a[0..1]);
    views a[0..1];
    ensures (0..1).fold(0, |acc, k| { acc + to_integer(a[k]) }) ==
        (0..0).fold(0, |acc, k| { acc + to_integer(a[k]) }) + to_integer(a[0]) by {
        execute();
        have 0 <= 0 by { simp(); }
        have 0 < 2147483647 by { simp(); }
        apply(integer_range_fold_append(
            (0..0).fold(0, |acc, k| { acc + to_integer(a[k]) })
        )) using {
            0 <= 0;
            0 < 2147483647;
        }
        simp();
    }
}
```

```expect
pass
```
