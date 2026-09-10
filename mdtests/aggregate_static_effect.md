# aggregate static writes require authorized field ownership

A struct static is external memory for ownership certification. Writing one of
its scalar fields without authorizing that field remains an error.

```c filename=aggregate_static_effect.c
struct state {
    int32 value;
};

int32 increment() {
    static struct state state;
    state.value = state.value + 1;
    return state.value;
}
```

```click
verifying "aggregate_static_effect.c";

int32 increment() {
    requires state.value < 1000;
    ensures result == old(state.value) + 1 by auto;
}
```

```expect
fail: outside the mutable footprint
```
