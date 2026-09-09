# A pointer reloaded after a call still aliases its local

```c filename=reloaded_local_pointer_alias.c
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
verifying "reloaded_local_pointer_alias.c";

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
    ensures result == 2 by {
        execute();
        simp();
    }
    produces pp[0..1];
}
```

```expect
pass
```
