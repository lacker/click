# An unfold pattern binds a scalar resource field

`let { field: name } = unfold(instance);` names the folded value of a C-typed
field, as a proof `match` arm names a constructor payload. The bound
name is a plain proof value that survives the unfold, so the scan loop's
invariant, its `decreases` measure, the post-loop facts, and the refold can
all name it.

`claim` scans a map whose prefix `[0, prefix)` is occupied for the first free
cell, which is the cell at `prefix`. The loop invariant bounds the scan by the
bound `p`, the loop exit proves `i == p` from the prefix facts, and the store
marks cell `p` occupied. The refold moves the field endpoint of the free data
suffix to `p + 1`, which leaves the claimed data cell `[p, p + 1)` owned
outside the resource for the contract to produce.

The mixed child-and-field form is
[`resource_unfold_binds_children_and_fields.md`](resource_unfold_binds_children_and_fields.md);
the dotted form is
[`resource_unfold_reads_the_opened_field.md`](resource_unfold_reads_the_opened_field.md).
`src/surface/tests/expansion_tests.rs` expands this fixture's smart sites and
reverifies the result.

```c filename=resource_unfold_binds_scalar_field.c
int32 claim(int32* data, int32* occupied, int32 capacity) {
    int32 i;
    i = 0;
    while (occupied[i] == 1) {
        i = i + 1;
    }
    occupied[i] = 1;
    return i;
}
```

```click
resource claimed_prefix(data: int32*, occupied: int32*, capacity: int32) {
    field prefix: int32;
    owns occupied[0..capacity];
    owns data[prefix..capacity];
    fact 0 <= prefix;
    fact prefix <= capacity;
    fact forall (k: int32) {
        0 <= k and k < prefix implies occupied[k] == 1
    };
    fact forall (k: int32) {
        prefix <= k and k < capacity implies occupied[k] == 0
    };
}

verifying "resource_unfold_binds_scalar_field.c";

int32 claim(int32* data, int32* occupied, int32 capacity) {
    consumes before: claimed_prefix(data, occupied, capacity);
    produces after: claimed_prefix(data, occupied, capacity);
    produces data[result..result + 1];
    requires before.prefix < capacity;
    ensures result == old(before.prefix);
    ensures to_integer(after.prefix) == to_integer(result + 1);
} by {
    let { prefix: p } = unfold(before);
    step();
    step();
    loop {
        decreases p - i;
        invariant 0 <= i and i <= p;
        owns occupied[0..capacity];
        initialize by close();
        maintain by {
            mark iteration;
            have i < p by {
                if i < p {
                    close();
                } else {
                    have i == p;
                    have p <= i by {
                        rewrite(i, p);
                        close();
                    }
                    have i < capacity by {
                        rewrite(i, p);
                        close();
                    }
                    have occupied[i] == 0 by {
                        instantiate(forall (k: int32) {
                            p <= k and k < capacity implies occupied[k] == 0
                        }, i);
                        close();
                    }
                    have not (occupied[i] == 1) by {
                        rewrite(occupied[i], 0);
                        close();
                    }
                    contradiction(occupied[i] == 1);
                }
            }
            have to_integer(i + 1) <= to_integer(p);
            have 0 <= to_integer(i + 1);
            step();
            have 0 <= i and i <= p;
            have 0 <= p by close();
            have 0 <= to_integer(0 - at(iteration, i) + p - 1) by {
                close() using {
                    0 <= at(iteration, i);
                    at(iteration, i) < p;
                    0 <= p;
                };
            }
            have to_integer(0 - at(iteration, i) + p - 1) < to_integer(0 - at(iteration, i) + p) by {
                close() using {
                    0 <= at(iteration, i);
                    at(iteration, i) < p;
                    0 <= p;
                };
            }
        }
    }
    have i == p by {
        if i < p {
            have occupied[i] == 1 by {
                instantiate(forall (k: int32) {
                    0 <= k and k < p implies occupied[k] == 1
                }, i);
                apply(0 <= i and i < p implies occupied[i] == 1);
            }
            contradiction(occupied[i] == 1);
        } else {
            have i == p;
            close();
        }
    }
    mark before_store;
    step();
    have to_integer(p + 1) <= to_integer(capacity);
    have 0 <= to_integer(p + 1);
    have forall (k: int32) {
        0 <= k and to_integer(k) < to_integer(p + 1) implies occupied[k] == 1
    } by {
        intro();
        intro();
        have to_integer(k) < to_integer(p + 1);
        if k < p {
            have at(before_store, occupied[k]) == 1 by {
                have at(before_store, 0) <= at(before_store, k) and
                        at(before_store, k) < at(before_store, p);
                instantiate(forall (j: int32) {
                    at(before_store, 0) <= at(before_store, j) and
                        at(before_store, j) < at(before_store, p) implies
                        at(before_store, occupied[j]) == at(before_store, 1)
                }, k);
                close();
            }
            have k != p;
            have k != i by {
                rewrite(i, p);
                close();
            }
            have separate(memory(occupied[i]), memory(occupied[k])) by {
                apply(click::separation::separate_elements(occupied, i, k));
            }
            have separate(statement(3).footprint, memory(occupied[k])) by {
                close() using { separate(memory(occupied[i]), memory(occupied[k])); };
            }
            have occupied[k] == at(before_store, occupied[k]) by {
                preserve(memory(occupied[k]), statement(3));
            }
            close();
        } else {
            have k <= p;
            have k == p;
            rewrite(k, p);
            close();
        }
    }
    have forall (k: int32) {
        to_integer(p + 1) <= to_integer(k) and k < capacity implies occupied[k] == 0
    } by {
        intro();
        intro();
        have to_integer(p + 1) <= to_integer(k);
        have p < p + 1;
        have p < k;
        have p <= k;
        have at(before_store, occupied[k]) == 0 by {
            have at(before_store, p) <= at(before_store, k) and
                    at(before_store, k) < at(before_store, capacity);
            instantiate(forall (j: int32) {
                at(before_store, p) <= at(before_store, j) and
                    at(before_store, j) < at(before_store, capacity) implies
                    at(before_store, occupied[j]) == at(before_store, 0)
            }, k);
            close();
        }
        have i < k by {
            rewrite(i, p);
            close();
        }
        have i != k;
        have separate(memory(occupied[i]), memory(occupied[k])) by {
            apply(click::separation::separate_elements(occupied, i, k));
        }
        have separate(statement(3).footprint, memory(occupied[k])) by {
            close() using { separate(memory(occupied[i]), memory(occupied[k])); };
        }
        have occupied[k] == at(before_store, occupied[k]) by {
            preserve(memory(occupied[k]), statement(3));
        }
        close();
    }
    let after = fold(claimed_prefix(data, occupied, capacity), { prefix: p + 1 });
    step();
    close();
}
```

```expect
pass
```
