# x86-64 `long double` layout

An extended-precision member contributes 16 bytes and 16-byte alignment to
aggregate layout. A typedef preserves the spelling for `sizeof` and fields.
This does not assign binary64 semantics to the member.

```c filename=long_double_layout.c
typedef long double extended_t;

struct Box {
    char prefix;
    extended_t value __attribute__((__aligned__(__alignof__(long double))));
    char suffix;
};

int32 long_double_size() {
    return sizeof(extended_t);
}

int32 long_double_box_size() {
    return sizeof(struct Box);
}
```

```click
verifying "long_double_layout.c";

int32 long_double_size() {
    ensures result == 16 by auto;
}

int32 long_double_box_size() {
    ensures result == 48 by auto;
}
```

```expect
pass
```
