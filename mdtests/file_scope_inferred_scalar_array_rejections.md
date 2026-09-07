# unsupported inferred file-scope array forms remain rejected

Only non-empty positional initializers infer a scalar array bound. Empty
initializers, designators, and aggregate arrays remain outside this slice.

```c filename=invalid.c
int32 designated[] = {[1] = 2};
int32 empty[] = {};

struct state {
    int32 value;
};

struct state aggregate[] = {{1}};

int32 read() {
    return 0;
}
```

```click
verifying "invalid.c";

int32 read() {
    ensures result == 0 by auto;
}
```

```expect
fail: inferred file-scope scalar array `designated` requires positional initializers
```
