# Heap-backed predicate contracts stay checked

A contract predicate may read the heap it describes. Its requirement and
postcondition should remain an ordinary checked contract proof across a
read-only C step, without requiring the author to unfold the predicate or
route through a compatibility proof.

```c filename=proof_heap_backed_predicate_contract.c
int32 proof_heap_backed_predicate_contract(int32 p[2]) {
    return p[0];
}
```

```click
verifying "proof_heap_backed_predicate_contract.c";

predicate ordered_pair(p: int32[2]) {
    p[0] <= p[1]
}

int32 proof_heap_backed_predicate_contract(int32 p[2]) {
    requires loadable(p[0..2]);
    views p[0..2];
    requires ordered_pair(p);
    ensures result == p[0];
    ensures remains_ordered: ordered_pair(p);
} by {
    step();
    simp();
}
```

```expect
pass
```
