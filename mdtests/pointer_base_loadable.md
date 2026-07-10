# loadable supports pointer-base segments

This checks that segment-form `loadable` uses the same pointer-base syntax
as mutable clauses. The requirement covers only the shifted one-cell range
`(p + 1)[0..1]`, and the function writes and reads exactly that cell.

```c filename=pointer_base_loadable.c
int32 pointer_base_loadable(int32* p) {
    p[1] = 9;
    return p[1];
}
```

```click
verifying "pointer_base_loadable.c";

int32 pointer_base_loadable(int32* p) {
    requires loadable((p + 1)[0..1]);
    requires write((p + 1)[0..1]);
    mutable (p + 1)[0..1] by frame;
    ensures returns_written: result == 9 by auto;
}
```

```expect
pass
```
