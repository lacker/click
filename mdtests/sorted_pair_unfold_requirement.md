# sorted_pair unfolds a requirement

This checks that `unfold(predicate)` is an explicit tactic. The predicate
fact from `requires sorted_pair(p)` is opaque until the proof script unfolds it.

```c filename=sorted_pair_unfold_requirement.c
int32 sorted_pair_unfold_requirement(int32 p[2]) {
    return 0;
}
```

```click
verifying "sorted_pair_unfold_requirement.c";

predicate sorted_pair(int32 p[2]) {
    p[0] <= p[1]
}

int32 sorted_pair_unfold_requirement(int32 p[2]) {
    requires loadable(p[0..2]);
    requires sorted_pair(p);
    ensures consequence: p[0] <= p[1] by {
        execute_rest();
        unfold(sorted_pair);
        simp();
    }
}
```

```expect
pass
```
