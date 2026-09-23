# Call-result existential needs an evaluated-load guard

The external call's existential is instantiated with the value of `a[i]` at
the call. Because the call may write the separate `b` range, the caller uses
`before_call` to name that evaluation snapshot. Click can prove the indexed
read was defined there, but spelling the existential with `at(...)` inserts
that viewability condition *inside* the quantifier. The call-produced fact has
the same body without that guard, so exact citation currently fails.

The missing *call-site proof route* is existential strengthening by a
binder-independent fact: from `V` and `exists path { P(path) }`, derive
`exists path { V and P(path) }`. Click can do this with `choose` when the
existential is an entry requirement, but cannot choose from this call-produced
fact. A future positive regression should use that fact and the proved
historical viewability, without assuming the witness or rewriting the C call.

```c filename=call_existential_evaluated_load_guard.c
extern int32 child(int32 *a, int32 *b, int32 n, int32 x);

int32 parent(int32 *a, int32 *b, int32 n, int32 i) {
    return child(a, b, n, a[i]);
}
```

```click
verifying "call_existential_evaluated_load_guard.c";

spec enum Path { Here }

function pick(x: int32, path: Path) -> int32 {
    match path { Path::Here => x }
}

extern int32 child(int32 *a, int32 *b, int32 n, int32 x) {
    views a[0..n];
    owns b[0..1];
    requires separate(memory(a[0..n]), memory(b[0..1]));
    ensures exists (path: Path) { pick(x, path) == x };
}

int32 parent(int32 *a, int32 *b, int32 n, int32 i) {
    requires 0 <= i;
    requires i < n;
    views a[0..n];
    owns b[0..1];
    requires separate(memory(a[0..n]), memory(b[0..1]));
    ensures result == result;
} by {
    mark before_call;
    let r = step(child(a, b, n, a[i]), {});
    have defined(at(before_call, a[i])) by { simp(); }
    have exists (path: Path) {
        pick(at(before_call, a[i]), path) == at(before_call, a[i])
    } by {
        assumption();
    }
    step();
    simp();
}
```

```expect
fail: current goal is an existential proposition
```
