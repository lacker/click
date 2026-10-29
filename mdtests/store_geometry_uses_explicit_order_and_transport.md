# Explicit facts replace automatic store searches

The wide store uses one stated endpoint order instead of walking an ambient
order chain. The array store may forget a compact run's possible write window;
the stated index inequality and explicit transport recover the selected old value.

```c filename=store_geometry.c
int32 wide_after(int32* a, int32 i, int32 middle, int32 j) {
    int64* w;
    a[i] = 5;
    w = (int64*)(void*)&a[j];
    *w = 0;
    return a[i];
}

int32 keep_first(int32* a, int32 i) {
    a[i] = 7;
    return a[0];
}
```

```click
verifying "store_geometry.c";

int32 wide_after(int32* a, int32 i, int32 middle, int32 j) {
    requires 0 <= i;
    requires i < middle;
    requires middle < j;
    requires j < 3;
    owns a[0..4];
    ensures result == 5;
} by {
    have i < j by solve() using { i < middle; middle < j; };
    step_until(function.exit);
}

int32 keep_first(int32* a, int32 i) {
    requires 0 <= i;
    requires i < 64;
    requires i != 0;
    owns a[0..64];
    ensures result == old(a[0]);
} by {
    step();
    have a[0] == old(a[0]) by {
        transport(old(a[0]) == old(a[0]), a[0] == old(a[0])) using {
            i != 0;
        };
    }
    step();
}
```

```expect
pass
```
