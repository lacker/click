# Quantified heap scopes stay checked

A quantified `have` may introduce a binder and prove a heap-backed body after
execution reaches a function outcome. The author should not need to flatten
that scope into an equivalent top-level postcondition proof.

```c filename=proof_quantified_heap_scope.c
int32 proof_quantified_heap_scope(int32 p[2]) {
    return p[0];
}
```

```click
verifying "proof_quantified_heap_scope.c";

int32 proof_quantified_heap_scope(int32 p[2]) {
    requires loadable(p[0..2]);
    views p[0..2];
    ensures result == p[0];
    ensures stable: forall (k: int32) {
        0 <= k and k < 2 implies p[k] == p[k]
    };
} by {
    step();
    have forall (k: int32) {
        0 <= k and k < 2 implies p[k] == p[k]
    } by {
        intro();
        intro();
        simp();
    }
    simp();
}
```

```expect
pass
```
