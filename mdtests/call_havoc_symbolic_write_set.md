# Call-havoc snapshots keep symbolic write sets distinct

Two callers have the same entry shape and the same call-havoc marker
allocation. The first call has an empty mutable range; the second may write
the loaded cell. The second caller must not inherit the first call's frozen
range evidence.

```c filename=call_havoc_symbolic_write_set_touch.c
int32 touch(int32 p[], int32 length) {
    return 0;
}
```

```c filename=call_havoc_symbolic_write_set_zero.c
int32 call_with_zero(int32 p[], int32 length) {
    int32 ignored;
    ignored = touch(p, length);
    return p[0];
}
```

```c filename=call_havoc_symbolic_write_set_positive.c
int32 call_with_positive(int32 p[], int32 length) {
    int32 ignored;
    ignored = touch(p, length);
    return p[0];
}
```

```click
verifying "call_havoc_symbolic_write_set_touch.c";
verifying "call_havoc_symbolic_write_set_zero.c";
verifying "call_havoc_symbolic_write_set_positive.c";

int32 touch(int32 p[], int32 length) {
    requires 0 <= length;
    mutable p[0..length];
    ensures result == 0;
} by {
    execute();
    frame();
    simp();
}

int32 call_with_zero(int32 p[], int32 length) {
    requires length == 0;
    owns p[0..1];
    mutable p[0..length];
    ensures result == old(p[0]);
} by {
    execute();
    frame();
    simp();
}

int32 call_with_positive(int32 p[], int32 length) {
    requires 1 <= length;
    owns p[0..1];
    mutable p[0..length];
    ensures result == old(p[0]);
} by {
    execute();
    frame();
    simp();
}
```

```expect
fail: old(p[0])
```
