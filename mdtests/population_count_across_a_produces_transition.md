# a population count across a `produces` transition

`produces object_ref(obj)` adds one unit to the population, so the post-state
count is the entry count plus one and `count(object_ref(obj)) == 1` does not
hold for an arbitrary entry count. The relation is already in the term — the
goal evaluates to `(v200000 + 1)` — so the refusal names the transition and asks
for that relation to be stated;
[`population_count_states_its_transition.md`](population_count_states_its_transition.md)
is it verifying.

```c filename=population_count_across_a_produces_transition.c
void object_retain(int32* obj) {
}
```

```click
abstract resource object_ref(obj: int32*);

verifying "population_count_across_a_produces_transition.c";

void object_retain(int32* obj) {
    owns object_ref(obj);
    requires count(object_ref(obj)) <= 1000;
    produces object_ref(obj);
    ensures count(object_ref(obj)) == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: `count(object_ref(obj))` changed since function entry: a `produces` or `consumes` transition in between moved it. The transition relates the two counts, so state that relation, as `ensures count(object_ref(obj)) == old(count(object_ref(obj))) + 1`.
```
