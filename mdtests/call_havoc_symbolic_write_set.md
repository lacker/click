# Call-havoc snapshots keep symbolic write sets distinct

Two callers share a call-havoc marker allocation. The first holds a view of
the loaded cell beside an empty owned range, so its call writes nothing; the
second owns the loaded cell, so its call may write it. The second caller
must not inherit the first call's frozen range evidence: its `old(p[0])`
claim fails. (A view cannot overlap an owner, so the second caller reads the
cell through its ownership rather than through a view; the two contracts
therefore differ in shape, and this fixture no longer pins the identical-shape
case.)

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
    owns p[0..length];
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 call_with_zero(int32 p[], int32 length) {
    requires length == 0;
    views p[0..1];
    owns p[0..length];
    ensures result == old(p[0]);
} by {
    execute();
    simp();
}

int32 call_with_positive(int32 p[], int32 length) {
    requires 1 <= length;
    owns p[0..length];
    ensures result == old(p[0]);
} by {
    execute();
    simp();
}
```

```expect
fail: old(p[0])
```
