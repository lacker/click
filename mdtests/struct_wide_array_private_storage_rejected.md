# A copied struct parameter cannot supply caller-owned storage

```c filename=wide.c
struct words { unsigned long data[2]; };
unsigned long read(struct words value) { return value.data[1]; }
```

```click
verifying "wide.c";
unsigned long read(struct words value) {
    views value.data;
    ensures result == value.data[1] by auto;
}
```

```expect
fail: its private storage cannot be an input resource
```
