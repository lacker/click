# produced populations are visible to ensured predicates

A function may create the first units of a declared-resource population. A
predicate in a later postcondition observes that post-state population count,
even when no entry requirement mentioned the resource family.

```c filename=produce_population.c
struct owner {
    int32 capacity;
};

void produce_population(struct owner* owner, int32 amount) {
    owner->capacity = amount;
}
```

```c filename=produce_population_pipeline.c
struct owner {
    int32 capacity;
};

void produce_population_pipeline(struct owner* owner, int32 amount) {
    produce_population(owner, amount);
}
```

```click
resource slot(owner: struct owner*) {
    views object(owner);
}

predicate valid_capacity(owner: struct owner*) {
    owner->capacity == count(slot(owner))
}

verifying "produce_population.c";
verifying "produce_population_pipeline.c";

void produce_population(struct owner* owner, int32 amount) {
    requires 0 <= amount;
    owns object(owner);
    mutable owner->capacity;
    produces amount of slot(owner);

    ensures valid_capacity(owner);
} by {
    execute();
    if 0 < amount {
        fold(amount of slot(owner));
        frame();
        simp();
    } else {
        apply(int32_ge_and_not_gt_implies_eq(amount, 0)) using {
            0 <= amount;
            not (0 < amount);
        }
        frame();
        simp();
    }
}

void produce_population_pipeline(struct owner* owner, int32 amount) {
    requires 0 <= amount;
    owns object(owner);
    produces amount of slot(owner);

    ensures valid_capacity(owner);
} by auto;
```

```expect
pass
```
