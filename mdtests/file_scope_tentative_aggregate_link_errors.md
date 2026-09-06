# tentative aggregate arrays require one compatible linked object

Tentative definitions may coalesce only when their aggregate-array types
match. A different bound is a conflicting declaration, even when neither
translation unit supplies an initializer.

```c filename=left.c
struct state {
    int32 value;
};

struct state table[2];

int32 left() {
    return table[0].value;
}
```

```c filename=right.c
struct state {
    int32 value;
};

struct state table[3];

int32 right() {
    return table[0].value;
}
```

```click
verifying "left.c";
verifying "right.c";

int32 left() {
    ensures result == 0 by auto;
}

int32 right() {
    ensures result == 0 by auto;
}
```

```expect
fail: conflicting declarations for aggregate global array `table`
```
