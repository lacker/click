# A consumed instance's field is refused with the unfold binding as the repair

`unfold(before)` consumes the instance, so its fields have nothing to read
afterwards. A loop invariant reads `old(..)` at the loop's entry, not at
function entry, so `old(before.prefix)` in the invariant below reads a field
of the consumed instance. The refusal names the field and the repair: bind
the field's folded value where the instance is unfolded,
`let { prefix: name } = unfold(before);`, as the passing twin
[`resource_unfold_binds_scalar_field.md`](resource_unfold_binds_scalar_field.md)
does.

```c filename=resource_unfold_field_binding_rejects_consumed_read.c
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

verifying "resource_unfold_field_binding_rejects_consumed_read.c";

int32 claim(int32* data, int32* occupied, int32 capacity) {
    consumes before: claimed_prefix(data, occupied, capacity);
    produces after: claimed_prefix(data, occupied, capacity);
    produces data[result..result + 1];
    requires before.prefix < capacity;
    ensures result == old(before.prefix);
    ensures after.prefix == result + 1;
} by {
    let { prefix: p } = unfold(before);
    step();
    step();
    loop {
        decreases p - i;
        invariant 0 <= i and i <= old(before.prefix);
        owns occupied[0..capacity];
        initialize by simp;
        preserve by {
            mark iteration;
            have i < p by {
                if i < p {
                    assumption();
                } else {
                    have i == p by {
                        apply(int32_le_and_not_lt_implies_eq(i, p)) using {
                            i <= p;
                            not (i < p);
                        }
                    }
                    have p <= i by {
                        rewrite(i == p);
                        normalize();
                    }
                    have i < capacity by {
                        rewrite(i == p);
                        assumption();
                    }
                    have occupied[i] == 0 by {
                        instantiate(forall (k: int32) {
                            p <= k and k < capacity implies occupied[k] == 0
                        }, i) using {
                            p <= i;
                            i < capacity;
                        }
                        assumption();
                    }
                    have not (occupied[i] == 1) by {
                        rewrite(occupied[i] == 0);
                        normalize();
                    }
                    contradiction(occupied[i] == 1);
                }
            }
            have i + 1 <= p by {
                apply(int32_increment_upper_bound(i, p)) using { i < p; }
            }
            have 0 <= i + 1 by {
                apply(int32_increment_lower_bound(i, 0, p)) using { 0 <= i; i < p; }
            }
            step();
            have 0 <= i and i <= p by { simp(); }
            have 0 <= p by { assumption(); }
            have 0 <= 0 - at(iteration, i) + p - 1 by {
                arithmetic() using {
                    0 <= at(iteration, i);
                    at(iteration, i) < p;
                    0 <= p;
                }
            }
            have 0 - at(iteration, i) + p - 1 < 0 - at(iteration, i) + p by {
                arithmetic() using {
                    0 <= at(iteration, i);
                    at(iteration, i) < p;
                    0 <= p;
                }
            }
            close_invariants();
        }
    }
    have i == p by {
        if i < p {
            have occupied[i] == 1 by {
                instantiate(forall (k: int32) {
                    0 <= k and k < p implies occupied[k] == 1
                }, i) using {
                    0 <= i;
                    i < p;
                }
                assumption();
            }
            contradiction(occupied[i] == 1);
        } else {
            apply(int32_le_and_not_lt_implies_eq(i, p)) using {
                i <= p;
                not (i < p);
            }
        }
    }
    mark before_store;
    step();
    have p + 1 <= capacity by {
        apply(int32_increment_upper_bound(p, capacity)) using { p < capacity; }
    }
    have 0 <= p + 1 by {
        apply(int32_increment_lower_bound(p, 0, capacity)) using { 0 <= p; p < capacity; }
    }
    have forall (k: int32) {
        0 <= k and k < p + 1 implies occupied[k] == 1
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < p + 1);
        if k < p {
            have at(before_store, occupied[k]) == 1 by {
                instantiate(forall (j: int32) {
                    at(before_store, 0) <= at(before_store, j) and
                        at(before_store, j) < at(before_store, p) implies
                        at(before_store, occupied[j]) == at(before_store, 1)
                }, k) using {
                    0 <= k;
                    k < p;
                }
                assumption();
            }
            have k != p by {
                apply(int32_lt_implies_neq(k, p)) using { k < p; }
            }
            have k != i by {
                rewrite(i == p);
                assumption();
            }
            transport(at(before_store, occupied[k]) == 1, occupied[k] == 1) using {
                at(before_store, occupied[k]) == 1;
                k != i;
            }
        } else {
            have k <= p by {
                apply(int32_lt_successor_implies_le(k, p)) using { k < p + 1; }
            }
            have k == p by {
                apply(int32_le_and_not_lt_implies_eq(k, p)) using {
                    k <= p;
                    not (k < p);
                }
            }
            rewrite(k == p);
            simp();
        }
    }
    have forall (k: int32) {
        p + 1 <= k and k < capacity implies occupied[k] == 0
    } by {
        intro();
        intro();
        extract(p + 1 <= k);
        extract(k < capacity);
        apply(int32_increment_strictly_increases(p, capacity)) using { p < capacity; }
        apply(int32_successor_le_implies_lt(p, k)) using {
            p < p + 1;
            p + 1 <= k;
        }
        apply(int32_lt_implies_le(p, k)) using { p < k; }
        have at(before_store, occupied[k]) == 0 by {
            instantiate(forall (j: int32) {
                at(before_store, p) <= at(before_store, j) and
                    at(before_store, j) < at(before_store, capacity) implies
                    at(before_store, occupied[j]) == at(before_store, 0)
            }, k) using {
                p <= k;
                k < capacity;
            }
            assumption();
        }
        have i < k by {
            rewrite(i == p);
            assumption();
        }
        have i != k by {
            apply(int32_lt_implies_neq(i, k)) using { i < k; }
        }
        transport(at(before_store, occupied[k]) == 0, occupied[k] == 0) using {
            at(before_store, occupied[k]) == 0;
            i != k;
        }
    }
    let after = fold(claimed_prefix(data, occupied, capacity), { prefix: p + 1 });
    step();
    simp();
}
```

```expect
fail: `before.prefix` reads a field of `before`, which is not held here; when `unfold(before)` consumed it, name the field's folded value where the instance is unfolded with `let { prefix: name } = unfold(before);`
```
