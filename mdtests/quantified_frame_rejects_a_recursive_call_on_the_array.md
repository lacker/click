# a recursive call is framed by its own write set, not by the caller facts

The recursive call owns `v[0..n - 1]` and may write every cell of it, and
the caller's own bounds on `n` say nothing about which. Preserving `v[k]`
across the call requires separation from that footprint. The explicit
separation goal is refused.

```c filename=quantified_frame_rejects_a_recursive_call_on_the_array.c
void zap(int32 *v, int32 n) {
    if (n <= 0) return;
    v[n - 1] = 0;
    zap(v, n - 1);
}
```

```click
verifying "quantified_frame_rejects_a_recursive_call_on_the_array.c";

void zap(int32 *v, int32 n) {
    decreases n;
    requires n <= 1000;
    owns v[0..n];
    ensures forall (k: int32) { 0 <= k and to_integer(k) < to_integer(n - 1) implies v[k] == old(v[k]) };
} by {
    branch {
        true => {
            step();
            close();
        }
        false => {}
    }
    step();
    have 0 <= to_integer(n - 1) by { close() using { 0 < n; }; }
    have to_integer(n - 1) <= 1000 by { close() using { 0 < n; n <= 1000; }; }
    mark before_call;
    step();
    have forall (k: int32) { 0 <= k and to_integer(k) < to_integer(n - 1) implies v[k] == at(before_call, v[k]) } by {
        intro(); intro();
        have separate(statement(2).footprint, memory(v[k])) by { close(); }
        preserve(memory(v[k]), statement(2));
    }
}
```

```expect
fail: goal: separate(region(4).footprint, v[…])
```
