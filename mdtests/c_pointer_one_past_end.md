# one-past pointers remain defined

Pointer arithmetic may form the one-past pointer for a viewed array, even
though that pointer cannot be dereferenced.

```c filename=c_pointer_one_past_end.c
int32* one_past_end(int32 data[], int32 n) {
    return data + n;
}
```

```click
verifying "c_pointer_one_past_end.c";

int32* one_past_end(int32 data[], int32 n) {
    requires 0 <= n;
    views data[0..n];
}
```

```expect
pass
```
