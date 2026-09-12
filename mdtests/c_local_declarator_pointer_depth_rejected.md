# A declaration list refuses a declarator of a different pointer depth

[`c_local_declarator_pointer_stars.md`](c_local_declarator_pointer_stars.md)
accepts `int32 *a, *b;`, where every declarator repeats the pointer depth the
type specifier writes. A list whose declarators would have different types is
refused by name instead of being typed from the first declarator's, so a
declaration that mixes depths is written as separate declarations.

```c filename=declarator_depth.c
int32 mixed_depth(int32 *p) {
    int32 *a = p, b;

    b = a[0];
    return b;
}
```

```click
verifying "declarator_depth.c";

int32 mixed_depth(int32* p) {
    views p[0..1];
    ensures result == p[0];
} by {
    execute();
    simp();
}
```

```expect
fail: a declarator with 0 pointer `*` in a declaration whose type specifier writes 1
```
