# a population count is not a wrapped total

A population count is a mathematical natural number. Two `produces k of
tok(o)` clauses at `k == 2000000000` are four billion units, and composing
them with the modular add made them a population of `-294967296` — so
`ensures count(tok(o)) < 0` verified of a function that had just produced
them. A total is formed now only where it is exact, so the two clauses stay
two facts and the negative population is never written down.

`counts_a_total_it_can_state` beside it is the other polarity: constant
quantities whose sum is a count are still added, and the count is that sum.

The call transition refuses the overflowing population before publishing a
post-count, and names the population and the missing addition bound.

```c filename=a_population_count_is_not_a_wrapped_total.c
void mint_n(int32* o, int32 n) {
}

void wraps_its_population(int32* o, int32 k) {
    mint_n(o, k);
    mint_n(o, k);
}

void counts_a_total_it_can_state(int32* o) {
    mint_n(o, 3);
    mint_n(o, 4);
}
```

```click
resource tok(o: int32*) {
}

verifying "a_population_count_is_not_a_wrapped_total.c";

void mint_n(int32* o, int32 n) {
    requires 0 < n;
    produces n of tok(o);
} by {
    execute();
    fold(n of tok(o));
    simp();
}

void wraps_its_population(int32* o, int32 k) {
    requires k == 2000000000;
    produces k of tok(o);
    produces k of tok(o);

    ensures count(tok(o)) < 0;
} by {
    execute();
    simp();
}

void counts_a_total_it_can_state(int32* o) {
    produces 3 of tok(o);
    produces 4 of tok(o);

    ensures count(tok(o)) == 7;
} by {
    execute();
    simp();
}
```

```expect
fail: a population count is a nonnegative `int32`
```
