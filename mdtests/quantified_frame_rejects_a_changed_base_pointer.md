# a quantified frame reads the pointer a parameter holds now

After `a = b`, `a[0] = 1` writes `b[0]`. A frame of `b[k]` must see the
store through the parameter's new value, so it is refused, although the
contract separates the entry values of `a` and `b`.

```c filename=quantified_frame_rejects_a_changed_base_pointer.c
void retarget(int32 *a, int32 *b, int32 n) {
    a = b;
    a[0] = 1;
}
```

```click
verifying "quantified_frame_rejects_a_changed_base_pointer.c";

void retarget(int32 *a, int32 *b, int32 n) {
    requires 0 < n;
    owns a[0..n];
    owns b[0..n];
    ensures forall (k: int32) { 0 <= k and k < n implies b[k] == old(b[k]) };
} by {
    step();
    step();
    have forall (k: int32) { 0 <= k and k < n implies b[k] == old(b[k]) } by { close(); }
}
```

```expect
fail: `solve` failed
```
