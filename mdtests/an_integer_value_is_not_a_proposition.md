# An integer value is not a proposition

A value written alone where a proposition is expected means `value == true`,
which needs a `bool` value. An integer is not read with C's nonzero truth,
so `requires count;` for an `int` parameter is a type error; write
`count != 0`.

```c filename=count.c
int identity(int count) { return count; }
```

```click
verifying "count.c";

int32 identity(int32 count) {
    requires count;
    ensures result == count;
} by {
    execute();
    simp();
}
```

```expect
fail: `count` has type int32, not bool, so it is not compared with `true` and is not a proposition on its own
```
