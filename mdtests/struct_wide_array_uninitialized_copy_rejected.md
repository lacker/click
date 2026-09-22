# Struct return copies must read every wide array element

```c filename=wide.c
struct words { unsigned long data[2]; };
struct words make(void) {
    struct words value;
    value.data[0] = 4294967296UL;
    return value;
}
```

```click
verifying "wide.c";
struct words make() {
    ensures result.data[0] == 4294967296u64 by auto;
}
```

```expect
fail: read of uninitialized storage
```
