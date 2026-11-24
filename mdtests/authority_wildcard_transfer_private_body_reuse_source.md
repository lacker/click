# A helper moves private membership between two pool authorities

The caller retains a member in each pool. Moving the third member changes
both totals and preserves its private memory and the retained members.

```c filename=wildcard_transfer_private_body.c
void move(int32* source, int32* destination, int32* p) {}
int32 lifecycle() {
    int32 source = 0;
    int32 destination = 0;
    int32* p = malloc(12);
    if (p == 0) return 0;
    p[0] = 1;
    p[1] = 2;
    p[2] = 3;
    move(&source, &destination, p);
    int32 result = p[0] + p[1] + p[2];
    free(p);
    return result;
}
```

```click
authorized resource slot(pool: int32*, p: int32*) { owns p[0..1]; }
verifying "wildcard_transfer_private_body.c";
void move(int32* source, int32* destination, int32* p) {
    requires source != destination;
    owns authority(slot(source, _));
    owns authority(slot(destination, _));
    consumes slot(source, p);
    requires defined(count(slot(destination, _)) + 1);
    produces slot(destination, p);
    ensures p[0] == old(p[0]);
    ensures count(slot(source, _)) == old(count(slot(source, _))) - 1;
    ensures count(slot(destination, _)) == old(count(slot(destination, _))) + 1;
} by {
    unfold(slot(source, p));
    fold(slot(destination, p));
    step_until(function.exit); close();
}
int32 lifecycle() { ensures result == 0 or result == 6; } by {
    step(); step(); step(); step(); step(); step();
    branch { true => { step_until(function.exit); close(); } false => {} }
    step(); step(); step();
    fold(authority(slot(&source, _)));
    fold(authority(slot(&destination, _)));
    fold(slot(&source, p));
    fold(slot(&source, p + 1));
    fold(slot(&destination, p + 2));
    step();
    unfold(slot(&source, p));
    have count(slot(&source, _)) == 1 by close();
    have count(slot(&destination, _)) == 2 by close();
    with(slot(&destination, p)) {
        with(slot(&source, p + 1)) {
            with(slot(&destination, p + 2)) { step(); step(); }
        }
    }
    unfold(slot(&destination, p));
    unfold(slot(&source, p + 1));
    unfold(slot(&destination, p + 2));
    unfold(authority(slot(&source, _)));
    unfold(authority(slot(&destination, _)));
    step_until(function.exit); close();
}
```

```expect
fail: Requires owns slot
```
