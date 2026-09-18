# A two-level loaded resource range unfolds on the pre-rewrite load names

A resource body that names its base through one load and its range endpoint
through another must unfold: the cells the unfold exposes are named by the same
load variables the kernel recomputes. See
[`issues/load-variable-naming-epoch.md`](../issues/load-variable-naming-epoch.md)
for the current divergence.

```c filename=load_variable_naming_epoch.c
struct arena {
    int32* data;
    int32 capacity;
};

struct region {
    struct arena* arena;
};

int32 f(struct region* r, struct arena* out) {
    return 0;
}
```

```click
spec enum Tag { T(int32) }

resource part(r: struct region*) {
    field tag: Tag;
    match tag {
        Tag::T(x) => {
            owns r->arena;
            owns r->arena->data;
            owns r->arena->capacity;
            owns r->arena->data[x..r->arena->capacity];
        },
    }
}

verifying "load_variable_naming_epoch.c";

int32 f(struct region* r, struct arena* out) {
    owns b: part(r);
    consumes object(out);
    ensures result == 0;
} by {
    match b.tag {
        Tag::T(x) => {
            unfold(b);
            execute();
            let b = fold(part(r), { tag: Tag::T(x) });
            simp();
        },
    }
}
```

```expect
pass
```
