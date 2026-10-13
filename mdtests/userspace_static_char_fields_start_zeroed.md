# User-space static `char` fields start zeroed

A static object without an initializer is zero-initialized (C11 6.7.9p10); a `const` one keeps that value in every call. Under the user-space
target a `char` array field holds `int8` cells and a `char *` field is an
`int8*` cell, and both start as zero and the null pointer.

```c filename=zeroed_char_fields.c
struct record {
    char name[4];
    char *label;
    int count;
};

static const struct record saved;

int zero_fields(void) {
    return saved.name[1] + (saved.label == 0) + saved.count;
}
```

```click
target "x86_64-linux-userspace";
verifying "zeroed_char_fields.c";

int32 zero_fields() {
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
