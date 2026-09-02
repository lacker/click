# loop back edge cannot resurrect an abstract resource

```c filename=take_token.c
int32 take_token(int32* p) {
    return 0;
}
```

```c filename=loop_token_lifetime_join.c
int32 loop_token_lifetime_join(int32* p) {
    int32 i;
    int32 status;
    i = 0;
    status = 0;
    while (i < 2) {
        status = take_token(p);
        i = i + 1;
    }
    status = take_token(p);
    return status;
}
```

```click
abstract resource can_complete(p: int32*);

verifying "loop_token_lifetime_join.c";
verifying "take_token.c";

int32 take_token(int32* p) {
    consumes can_complete(p);
    ensures result == 0 by auto;
}

int32 loop_token_lifetime_join(int32* p) {
    consumes can_complete(p);
    ensures result == 0;
} by {
    step();
    step();
    step();
    step();
    loop {
        invariant i >= 0;
        invariant i <= 1;
    }
    step();
    step();
    simp();
}
```

```expect
fail: resource ownership
```
