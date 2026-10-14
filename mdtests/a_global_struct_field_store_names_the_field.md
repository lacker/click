# A memory-history refusal names the global struct field a loop writes

The loop writes `g.b` through `p`, four bytes at offset 4 of the global `g`.
Exactly one field of `struct pair` occupies exactly those bytes, so the
memory-history sentence names the field, `g.b`, instead of the byte offset
`g+4`.

```c filename=a_global_struct_field_store_names_the_field.c
struct pair {
    int32 a;
    int32 b;
};

struct pair g;

int32 loop_writes_field() {
    int32* p;
    int32 i;
    p = &g.b;
    i = 0;
    while (i < 2) {
        p[0] = 9;
        i = i + 1;
    }
    return g.b;
}
```

```click
verifying "a_global_struct_field_store_names_the_field.c";

int32 loop_writes_field() {
    owns g.a;
    owns g.b;
    requires g.b == 3;
    ensures result == 3;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases 2 - i;
        invariant i >= 0;
        invariant i <= 2;
    }
    execute();
    simp();
}
```

```expect
fail: right side evaluated to 3; `g.b` may have changed since earlier in this function
```
