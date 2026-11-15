# A nested index read retains its entry state

Changing the index cell after reading `a[*p]` does not change the index used
by the saved value. Its postcondition spells both reads at entry.

```c filename=nested_index.c
int lookup_then_change(int *a, int *p) {
    int value = a[*p];
    *p = 0;
    return value;
}
```

```click
verifying "nested_index.c";
int32 lookup_then_change(int32* a, int32* p) {
    views a[0..4];
    owns *p;
    requires 0 <= *p;
    requires *p < 4;
    requires separate(memory(*p), memory(a[0..4]));
    ensures result == old(a[*p]);
}
```

```expect
pass
```
