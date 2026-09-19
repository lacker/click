# applying a `views` theorem needs the range the theorem states

A theorem's `views` clause is a premise like any other, so an application that
cannot establish it is refused rather than granted. The contract below holds
`views a[0..2]` and applies a theorem stated over `v[0..3]`: two elements are
not three, and holding a resource over part of a range establishes nothing
about the rest of it.

The refusal names the clause as the theorem wrote it, the arguments its own
names were bound to, and the fact that instantiation asks for. It spells the
clause as `viewable(v[lo..hi])`, which is the form the reader has to put in the
`using` list, since a `using` list holds propositions and a `views` statement is
not one.

```c filename=views_theorem_premise_must_be_established.c
int32 ignore(int32 a[]) {
    return 0;
}
```

```click
verifying "views_theorem_premise_must_be_established.c";

theorem element_of_a_viewed_range(v: int32[], lo: int32, hi: int32, k: int32) {
    views v[lo..hi];
    requires lo <= k;
    requires k < hi;
    ensures to_integer(v[k]) == to_integer(v[k]) by {
        simp();
    }
}

int32 ignore(int32 a[]) {
    views a[0..2];
    ensures result == 0;
} by {
    step();
    apply(element_of_a_viewed_range(a, 0, 3, 1)) using {
        viewable(a[0..2]);
    }
    simp();
}
```

```expect
fail: required exact fact for theorem `element_of_a_viewed_range` is unavailable: requirement 1 `viewable(v[lo..hi])` with v = a, lo = 0, hi = 3 instantiates to
```
