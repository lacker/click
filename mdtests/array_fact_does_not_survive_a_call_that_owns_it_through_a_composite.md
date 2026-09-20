# epoch attack 9: the callee's write set reaches the array through a composite

`scribble` names no memory range at all: it owns `vecbox(b, n)`, and the range
it writes is inside that composite. A write set that did not expand the
composite would be empty, and an empty write set is separate from everything —
so the fact would survive a call that wrote `a[0]`.

It does not, because the checked write set on the edge *is* the expansion:
`checked_owned_memory_ranges` expands each owned requirement through its
composite definitions and collects every owned range of the expansion, so the
edge here carries one range, based at `a`. An array parameter is not proven
distinct from itself, and the fact stops at the call.

```c filename=array_fact_does_not_survive_a_call_that_owns_it_through_a_composite.c
void scribble(int32 b[], int32 n) {
    b[0] = 1;
}

void caller(int32 a[], int32 n) {
    scribble(a, n);
}
```

```click
resource vecbox(p: int32*, n: int32) {
    owns p[0..n];
    fact 0 < n;
}

verifying "array_fact_does_not_survive_a_call_that_owns_it_through_a_composite.c";

function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}

void scribble(int32 b[], int32 n) {
    owns vecbox(b, n);
} by {
    unfold(vecbox(b, n));
    execute();
    fold(vecbox(b, n));
    simp();
}

void caller(int32 a[], int32 n) {
    requires 0 < n;
    owns vecbox(a, n);
} by {
    unfold(vecbox(a, n));
    have 0 <= 0 by { simp(); }
    have icount(a, 0, 0) == 0 by {
        unfold(icount(a, 0, 0)) using { 0 <= 0; }
        normalize();
    }
    fold(vecbox(a, n));
    step();
    have icount(a, 0, 0) == 0 by { simp(); }
    execute();
    simp();
}
```

```expect
fail: a fact about `a` as a whole does not carry across the call. Only a step the kernel proves leaves the whole object alone carries one, and a stated `separate(...)` is not read here.
```
