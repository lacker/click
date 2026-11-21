# Goal refinements follow the focused contract claim

```c filename=focused_claims.c
int refine(int x, int y) { return x; }
int choose_value(int n) { return n; }
```

```click
verifying "focused_claims.c";

int32 refine(int32 x, int32 y) {
    requires x == y;
    ensures forall (k: int32) { result == y and k == k };
    ensures result == y;
} by {
    step_until(function.exit);
    let k = intro();
    rewrite(y, x);
    all {
        result == x => { known(); }
        k == k => { normalize(); }
    }
    rewrite(y, x);
    known();
}

int32 choose_value(int32 n) {
    ensures exists (k: int32) { k == result };
    ensures result == n;
} by {
    step_until(function.exit);
    witness(n);
    known();
    known();
}
```

```expect
pass
```
