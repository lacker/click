# sibling blocks may reuse a local name

```c filename=c_block_scope_sibling_redeclarations.c
int32 siblings(int32 c) {
    int32 r;
    if (c < 0) { int32 v = 1; r = v; } else { int32 v = 2; r = v; }
    return r;
}
```

```click
verifying "c_block_scope_sibling_redeclarations.c";

int32 siblings(int32 c) {
    requires c >= 0;
    ensures result == 2 by auto;
}
```

```expect
pass
```
