# consumed population predicates require the actual consumption

Declaring consumption does not perform it. Updating concrete capacity without
consuming the matching members cannot restore the private accounting invariant.
The proof rewrites the final capacity equation to its entry counts and the
checked subtraction, then checks it using only the bounds on the amount.

```c filename=consume_population.c
struct owner {
    int32 used;
    int32 capacity;
};

void consume_population(struct owner* owner, int32 amount) {
    owner->capacity = owner->capacity - amount;
}
```

```click
authorized resource slot(owner: struct owner*) {
}

authorized abstract resource item(owner: struct owner*, id: int32);

resource accounting(owner: struct owner*) {
    owns owner->used;
    owns owner->capacity;
    owns authority(slot(owner));
    owns authority(item(owner, _));
    fact 0 <= owner->used;
    fact owner->used == count(item(owner, _));
    fact owner->capacity == owner->used + count(slot(owner));
}

predicate valid_capacity(owner: struct owner*) {
    0 <= owner->used and
    owner->used == count(item(owner, _)) and
    owner->capacity == owner->used + count(slot(owner))
}

verifying "consume_population.c";

void consume_population(struct owner* owner, int32 amount) {
    requires valid_capacity(owner);
    requires 0 <= amount;
    requires amount <= count(slot(owner));
    requires defined(owner->capacity - amount);
    owns accounting(owner);
    consumes amount of slot(owner);

    ensures valid_capacity(owner);
} by {
    with(accounting(owner)) {
        unfold(valid_capacity(owner));
        step();
        have to_integer(owner->used) == to_integer(old(owner->used)) by { close(); }
        have to_integer(old(owner->capacity)) ==
            to_integer(old(owner->used)) + to_integer(old(count(slot(owner)))) by {
            close();
        }
        have owner->capacity == old(owner->capacity) - amount;
        have to_integer(owner->capacity) ==
            to_integer(owner->used) + to_integer(count(slot(owner))) by {
            rewrite(to_integer(owner->capacity),
                to_integer(old(owner->capacity)) - to_integer(amount));
            rewrite(to_integer(old(owner->capacity)),
                to_integer(old(owner->used)) + to_integer(old(count(slot(owner)))));
            rewrite(to_integer(owner->used), to_integer(old(owner->used)));
            close() using {
                0 <= amount;
                amount <= old(count(slot(owner)));
            };
        }
    }
    step_until(function.exit);
    unfold(valid_capacity(owner));
    close();
}
```

```expect
fail: `consume_population.contract` proof step have body tactic 4: arithmetic read the current goal as an Integer linear claim; no combination of the listed premises proves it
```
