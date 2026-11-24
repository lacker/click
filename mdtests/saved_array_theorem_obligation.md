# A saved array argument retains a writable viewability obligation

```c filename=saved_array.c
void keep(int32 *p) {}
```

```click
verifying "saved_array.c";

theorem visible(a: int32[]) {
    views a[0..1];
    ensures true by { close(); }
}

void keep(int32 *p) {
    views p[0..1];
    ensures true;
} by {
    mark before;
    apply(visible(at(before, p)));
    step_until(function.exit);
}
```

```expect
pass
```
