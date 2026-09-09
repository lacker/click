# A reloaded pointer cannot prove an inconsistent local result

```c filename=reloaded_local_pointer_impossible.c
void keep(int32** pp) {
}

int32 reloaded_store_hits_local(int32** pp) {
    int32 x = 1;
    int32* q;
    *pp = &x;
    keep(pp);
    q = *pp;
    if (q == &x) {
        *q = 2;
    }
    return x;
}
```

```click
verifying "reloaded_local_pointer_impossible.c";

void keep(int32** pp) {
    requires loadable(pp[0..1]);
    consumes pp[0..1];
    mutable pp[0..1];
    ensures pp[0] == old(pp[0]);
    produces pp[0..1];
}

int32 reloaded_store_hits_local(int32** pp) {
    requires loadable(pp[0..1]);
    consumes pp[0..1];
    mutable pp[0..1];
    ensures result == 7 by {
        execute();
        simp();
    }
    produces pp[0..1];
}
```

```expect
fail: left side evaluated to 2, right side evaluated to 7
```
