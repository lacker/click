# a C proof applies a theorem that states `views`

A theorem's `views` clause is a hypothesis, so applying it from a C proof owes
that hypothesis. The C side has a resource context, and what discharges the
premise there is the readability the contract's own `views a[0..3]` already
gives: the clause is lowered to the same `loadable` fact the theorem's premise
lowers to, so the two meet as one exact fact.

The premise is named in the `using` list by its fact form, `loadable(a[0..3])`.
A `using` list is a list of propositions and stays one — there is no `views`
statement inside it — which is also why the theorem's requirement is printed in
that form when an application cannot discharge it; see
`mdtests/views_theorem_premise_must_be_established.md`.

The range here has a constant extent, so nothing else is owed. A symbolic range
also owes its valid-extent facts at the application, in the form
`0 <= count` and `count <= 1073741823`.

```c filename=c_proof_applies_a_views_theorem.c
int32 second(int32 a[]) {
    return a[1];
}
```

```click
verifying "c_proof_applies_a_views_theorem.c";

function element(v: int32[], k: int32) -> Integer {
    to_integer(v[k])
}

theorem element_of_a_viewed_range(v: int32[], lo: int32, hi: int32, k: int32) {
    views v[lo..hi];
    requires lo <= k;
    requires k < hi;
    ensures element(v, k) == to_integer(v[k]) by {
        unfold(element(v, k));
        simp();
    }
}

int32 second(int32 a[]) {
    views a[0..3];
    ensures element(a, 1) == to_integer(result);
} by {
    step();
    apply(element_of_a_viewed_range(a, 0, 3, 1)) using {
        loadable(a[0..3]);
    }
    simp();
}
```

```expect
pass
```
