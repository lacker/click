# An indexed store exposes its strict bounds

```c filename=indexed_store.c
void set(int32* data, int32 len, int32 i) {
    data[i] = 100;
    return;
}
```

```click
verifying "indexed_store.c";

void set(int32* data, int32 len, int32 i) {
    owns data[0..len];
    requires 0 <= i and i < len;
} by {
    step() by { close(); }
    step();
}
```

```expect
pass
```
