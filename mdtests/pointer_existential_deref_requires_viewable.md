# Choosing a pointer does not make it dereferenceable

An existential pointer witness may be used for pointer reasoning, but it does
not create memory permission or initialization facts. Dereferencing an
arbitrary pointer must still be rejected.

```c filename=pointer_existential_deref_requires_loadable.c
int32 pointer_existential_deref_requires_loadable(int32* p) {
    return 0;
}
```

```click
verifying "pointer_existential_deref_requires_loadable.c";

int32 pointer_existential_deref_requires_loadable(int32* p) {
    requires has_null: exists (q: int32*) { q == 0 };
    ensures dereference_is_not_implied: exists (r: int32*) { defined(r[0]) } by {
        execute();
        choose(q from requirement has_null);
        witness(r = q);
        simp();
    }
}
```

```expect
fail: did not complete the retained existential Proof
```
