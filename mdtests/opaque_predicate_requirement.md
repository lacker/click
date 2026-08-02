# opaque predicate requirements can be reused

This checks the first predicate slice: `.click` can define a named predicate,
use it in a requirement, and prove the exact same opaque predicate later. The
predicate body is not unfolded by default.

```c filename=opaque_predicate_requirement.c
int32 opaque_predicate_requirement(int32 p[2]) {
    return 0;
}
```

```click
verifying "opaque_predicate_requirement.c";

predicate sorted_pair(p: int32[2]) {
    p[0] <= p[1]
}

int32 opaque_predicate_requirement(int32 p[2]) {
    requires sorted_pair(p);
    ensures still_sorted: sorted_pair(p) by auto;
}
```

```expect
pass
```
