# produced populations are visible to ensured predicates

A function supplied with authority for an empty resource family can create its
first members. A predicate in its postcondition observes the count after that
checked birth. An ordinary helper call transfers the same authority and
requires the same empty-family fact; neither operation assumes an arbitrary
entry population is empty.

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
authorized resource slot(owner: struct owner*) {
}

predicate valid_capacity(owner: struct owner*) {
    owner->capacity == count(slot(owner))
}

verifying "produce_population.c";
verifying "produce_population_pipeline.c";

void produce_population(struct owner* owner, int32 amount) {
    requires 0 <= amount;
    owns authority(slot(owner));
    requires count(slot(owner)) == 0;
    produces amount of slot(owner);
    owns owner->capacity;

    ensures valid_capacity(owner);
} by {
    step();
    if 0 < amount {
        fold(amount of slot(owner));
        step_until(function.exit); close();
    } else {
        have amount == 0;
        step_until(function.exit); close();
    }
}

void produce_population_pipeline(struct owner* owner, int32 amount) {
    requires 0 <= amount;
    owns authority(slot(owner));
    requires count(slot(owner)) == 0;
    owns *owner;
    produces amount of slot(owner);

    ensures valid_capacity(owner);
}
```

```expect
pass
```
