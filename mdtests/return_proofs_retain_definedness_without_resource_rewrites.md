# Return proofs retain definedness without a resource rewrite

These `have` steps establish the arithmetic domain in the outcome proof.
The contract goal consumes that evidence through ordinary obligation checking,
and proof completion retains the established contract claim. No resource rewrite or
reconstruction of the proof facts from the C execution trace is needed.
```c filename=return_definedness.c
int32 g[4];

int32 planned(int32 u) {
    int32 r;
    g[u] = 7;
    r = g[0];
    r = r + 1;
    return r;
}
```
```click
verifying "return_definedness.c";

int32 planned(int32 u) {
    requires 0 <= u;
    requires u < 4;
    requires g[0] < 100;
    owns g[0..4];
    ensures result == 8 or to_integer(result) == to_integer(old(g[0]) + 1);
} by {
    have defined(old(g[0])) by {
        instantiate(forall (k: int32) { 0 <= k and k < 4 implies defined(old(g[k])) }, 0);
        close();
    }
    have old(g[0]) < 2147483647 by {
        have 100 <= 2147483647 by close();
        apply(click::integer::int32_less_than_less_equal_transitive(old(g[0]), 100, 2147483647));
    }
    have defined(old(g[0]) + 1) by {
        apply(click::integer::int32_increment_below_max_is_defined(old(g[0])));
        close();
    }
    step();
    step();
    step();
    if u == 0 {
        step();
        step();
        step();
        have result == 8 or defined(old(g[0]) + 1);
        close();
    } else {
        step();
        step();
        step();
        have result == 8 or defined(old(g[0]) + 1);
        close();
    }
}

```
```expect
pass
```
