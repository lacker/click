# aggregate globals require one linked initialized definition

Tentative aggregate definitions may coalesce, but two translation units that
both provide initialized definitions still violate the one-object invariant.

```c filename=left.c
struct state {
    int32 value;
};

struct state shared = {1};

int32 left() {
    return shared.value;
}
```

```c filename=right.c
struct state {
    int32 value;
};

struct state shared = {2};

int32 right() {
    return shared.value;
}
```

```click
verifying "left.c";
verifying "right.c";

int32 left() {
    ensures result == 1 by auto;
}

int32 right() {
    ensures result == 2 by auto;
}
```

```expect
fail: multiple definitions of aggregate global `shared`
```
