# a block-scoped struct pointer may not shadow a parameter

```c filename=c_block_scope_rejects_shadowing_struct_pointer.c
struct S { int32 a; int32 b; };
struct T { int32 b; int32 z; };

int32 pick2(struct S* p, struct T* q, int32 c) {
    if (c < 0) { struct T *p = q; p->b = 1; }
    return p->b;
}
```

```click
verifying "c_block_scope_rejects_shadowing_struct_pointer.c";

int32 pick2(struct S* p, struct T* q, int32 c) {
    ensures result == 7 by auto;
}
```

```expect
fail: `p` is already declared in an enclosing scope
```
