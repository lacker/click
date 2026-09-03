# calloc zeroes matching struct fields

The modeled `calloc` form accepts a runtime count of complete struct objects
when the element size matches the target struct pointer. All supported scalar
and pointer fields in the fresh storage read as their all-bits-zero values.

```c filename=calloc_zeroed_struct.c
struct pair {
    uint8 tag;
    int32 value;
    struct pair* next;
};

int32 calloc_zeroed_struct() {
    struct pair* pair = calloc(1, sizeof(struct pair));
    if (pair == 0) {
        return 1;
    }
    int32 result = pair->tag + pair->value + (pair->next != 0);
    free(pair);
    return result;
}
```

```click
verifying "calloc_zeroed_struct.c";

int32 calloc_zeroed_struct() {
    ensures result == 0 or result == 1 by auto;
}
```

```expect
pass
```
