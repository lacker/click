# Explicit transport inside `have` sees certified execution effects

An expanded pure proof may transport an exact store fact across a later,
disjoint store. The simple `transport(...) using` step must receive the same
certified execution effects as ordinary frontier transport; `rewrite` must not
search those effects as a fallback.

```c filename=pure_have_explicit_transport_uses_execution_effects.c
int32 set_second_return_first(int32 p[2]) {
    p[1] = 9;
    return p[0];
}
```

```click
verifying "pure_have_explicit_transport_uses_execution_effects.c";

predicate first_is_seven(p: int32[]) {
    p[0] == 7
}

int32 set_second_return_first(int32 p[2]) {
    requires first_is_seven(p);
    consumes p[0..2];
    mutable p[1..2];

    produces p[0..2];
    ensures result == 7;
} by {
    unfold(first_is_seven);
    step();
    have p[0] == 7 by {
        transport(
            old(p[0]) == 7,
            p[0] == 7
        ) using {
            old(p[0]) == 7;
        }
        assumption();
    }
    step();
    frame();
    simp();
}
```

```expect
pass
```
