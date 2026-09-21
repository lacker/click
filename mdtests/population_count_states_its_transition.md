# a population count that states its own transition

The positive side of
[`population_count_across_a_produces_transition.md`](population_count_across_a_produces_transition.md):
the clause that refusal prints. The count bounds are what the transition's own
overflow condition needs; the relation itself is what the `produces` establishes.

```c filename=population_count_states_its_transition.c
void object_retain(int32* obj) {
}
```

```click
abstract resource object_ref(obj: int32*);

verifying "population_count_states_its_transition.c";

void object_retain(int32* obj) {
    owns object_ref(obj);
    requires count(object_ref(obj)) >= 1;
    requires count(object_ref(obj)) <= 1000;
    produces object_ref(obj);
    ensures count(object_ref(obj)) == old(count(object_ref(obj))) + 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
