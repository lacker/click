# recursive resource rejects mutual cycles

Guarded direct self-recursion has a one-layer interpretation. Mutually
recursive resource definitions remain outside that deliberately small model.

```c filename=recursive_resource_rejects_mutual_cycle.c
int32 recursive_resource_rejects_mutual_cycle(int32* p) {
    return 0;
}
```

```click
resource left(p: int32*) {
    if p != 0 {
        contains right(p);
    }
}

resource right(p: int32*) {
    if p != 0 {
        contains left(p);
    }
}

verifying "recursive_resource_rejects_mutual_cycle.c";

int32 recursive_resource_rejects_mutual_cycle(int32* p) {
    ensures result == 0 by auto;
}
```

```expect
fail: composite resource cycle
```
