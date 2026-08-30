theorem int32_equality_transitive(first: int32, second: int32, third: int32) {
    requires first == second;
    requires second == third;

    ensures first == third by {
        simp();
    }
}

resource empty_vector(owner: struct vector*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact owner->len == 0;
    fact 1 <= owner->cap;
    fact separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
}

resource nonempty_vector(owner: struct vector*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 1 <= owner->len;
    fact owner->len <= owner->cap;
    fact separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
}

resource vector_storage(owner: struct vector*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
    fact loadable(owner->data[0..owner->len]);
    fact separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
}

resource allocated_vector(owner: struct vector*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    contains allocation(owner->data, owner->cap * 4);
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
    fact 1 <= owner->cap;
    fact owner->cap <= 536870911;
    fact loadable(owner->data[0..owner->len]);
    fact separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
}

verifying "vector_init.c";
verifying "vector_len.c";
verifying "vector_get.c";
verifying "vector_set.c";
verifying "vector_fill.c";
verifying "vector_replace_if.c";
verifying "vector_clear.c";
verifying "vector_pipeline.c";
verifying "vector_copy.c";
verifying "vector_grow.c";
verifying "vector_push.c";
verifying "allocated_vector_push.c";

int32 vector_copy(
    int32 dst[],
    int32 src[],
    int32 length,
    int32 dst_capacity,
    int32 src_capacity
) {
    requires 0 <= length;
    requires length <= dst_capacity;
    requires length <= src_capacity;
    requires 1 <= dst_capacity;
    requires 1 <= src_capacity;
    owns dst[0..dst_capacity];
    views src[0..src_capacity];
    requires separate(memory(dst[0..dst_capacity]), memory(src[0..src_capacity]));
    mutable dst[0..length];
    ensures result == length;
    ensures forall (k: int32) {
        0 <= k and k < length implies src[k] == old(src[k])
    };
    ensures forall (k: int32) {
        0 <= k and k < length implies dst[k] == old(src[k])
    };
} by {
    step();
    step();
    loop {
        invariant 0 <= i;
        invariant i <= length;
        invariant forall (k: int32) { 0 <= k and k < i implies dst[k] == old(src[k]) };
        mutable dst[0..length] by frame;
        initialize by {
            have 0 <= i by {
                normalize();
            }
            have i <= length by {
                assumption();
            }
            have forall (k: int32) { 0 <= k and k < i implies dst[k] == old(src[k]) } by {
                normalize();
            }
        }
        preserve by {
            step();
            step();
            close_invariants();
        }
    }
    have i == length by {
        apply(int32_le_and_not_lt_implies_eq(at(loop(0).exit, i), at(loop(0).exit, length))) using {
            at(loop(0).exit, i) <= at(loop(0).exit, length);
            not at(loop(0).exit, i) < at(loop(0).exit, length);
        }
        assumption();
    }
    have forall (k: int32) { 0 <= k and k < length implies dst[k] == old(src[k]) } by {
        intro();
        intro();
        instantiate(forall (k: int32) { at(loop(0).exit, 0) <= at(loop(0).exit, k) and at(loop(0).exit, k) < at(loop(0).exit, i) implies at(loop(0).exit, dst[k]) == old(src[k]) }, k) using {
            0 <= k and k < length;
            i == length;
        }
        assumption();
    }
    step();
    frame() using {
    }
    have result == length by {
        assumption();
    }
    have forall (k: int32) { 0 <= k and k < length implies src[k] == old(src[k]) } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < length);
        transport(old(src[k]) == old(src[k]), src[k] == old(src[k])) using {
            0 <= length;
            0 <= k;
            k < length;
            length <= dst_capacity;
            length <= src_capacity;
            1 <= dst_capacity;
            1 <= src_capacity;
            at(statement(0).entry, loadable(dst[0..dst_capacity]));
            at(statement(0).entry, loadable(src[0..src_capacity]));
            separate(memory(dst[0..dst_capacity]), memory(src[0..src_capacity]));
        }
        assumption();
    }
    have forall (k: int32) { 0 <= k and k < length implies dst[k] == old(src[k]) } by {
        assumption();
    }
    assumption();
    assumption();
    assumption();
    assumption();
}

int32 vector_grow(struct vector* owner) {
    let entry_length = old(owner->len);
    let entry_capacity = old(owner->cap);

    requires owner->cap <= 536870910;
    consumes allocated_vector(owner);
    mutable owner->data, owner->cap;
    produces allocated_vector(owner);
    ensures result == 0 or result == 1;
    ensures owner->len == entry_length;
    ensures result == 0 implies owner->cap == entry_capacity;
    ensures result == 0 implies owner->data == old(owner->data);
    ensures result == 1 implies owner->cap == entry_capacity + 1;
    ensures forall (k: int32) {
        0 <= k and k < entry_length implies
            owner->data[k] == old(owner->data[k])
    };
} by {
    unfold(allocated_vector(owner));
    have owner->cap < 2147483647 by {
        apply(int32_le_lt_transitive(owner->cap, 536870910, 2147483647)) using {
            owner->cap <= 536870910;
        }
        assumption();
    }
    have (owner->cap + 1) <= 536870911 by {
        apply(int32_le_lt_transitive(owner->cap, 536870910, 536870911)) using {
            owner->cap <= 536870910;
        }
        apply(int32_increment_upper_bound(owner->cap, 536870911)) using {
            owner->cap < 536870911;
        }
        assumption();
    }
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    have 0 <= owner->len by {
        assumption();
    }
    have owner->len <= owner->cap by {
        assumption();
    }
    have 1 <= new_capacity by {
        have 1 <= (owner->cap + 1) by {
            apply(int32_increment_lower_bound(owner->cap, 1, 2147483647)) using {
                1 <= owner->cap;
                owner->cap < 2147483647;
            }
            assumption();
        }
        transport(1 <= (owner->cap + 1), 1 <= new_capacity) using {
            1 <= (owner->cap + 1);
        }
        assumption();
    }
    have owner->len <= old_capacity by {
        assumption();
    }
    have owner->len <= new_capacity by {
        have owner->len <= (owner->cap + 1) by {
            apply(int32_increment_lower_bound(owner->cap, owner->len, 2147483647)) using {
                owner->len <= owner->cap;
                owner->cap < 2147483647;
            }
            assumption();
        }
        transport(owner->len <= (owner->cap + 1), owner->len <= new_capacity) using {
            owner->len <= (owner->cap + 1);
        }
        assumption();
    }
    have new_capacity <= 536870911 by {
        assumption();
    }
    have loadable(old_data[0..old_capacity]) by {
        transport(loadable(old(owner->data[0..owner->cap])), loadable(old_data[0..old_capacity])) using {
            loadable(old(owner->data[0..owner->cap]));
        }
        assumption();
    }
    if new_data == 0 {
        have loadable(owner->data[0..owner->cap]) by {
            transport(loadable(old(owner->data[0..owner->cap])), loadable(owner->data[0..owner->cap])) using {
                loadable(old(owner->data[0..owner->cap]));
            }
            assumption();
        }
        step();
        step();
        have forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) } by {
            intro();
            intro();
            extract(0 <= k);
            extract(k < old(owner->len));
            transport(old(owner->data[k]) == old(owner->data[k]), owner->data[k] == old(owner->data[k])) using {
                0 <= k;
                k < old(owner->len);
            }
            assumption();
        }
        fold(allocated_vector(owner));
        frame() using {
        }
        have result == 0 by {
            normalize();
        }
        have result == 0 or result == 1 by {
            normalize();
        }
        have owner->len == old(owner->len) by {
            normalize();
        }
        have result == 0 implies owner->cap == old(owner->cap) by {
            normalize();
        }
        have result == 0 implies owner->data == old(owner->data) by {
            normalize();
        }
        have result == 1 implies owner->cap == (old(owner->cap) + 1) by {
            normalize();
        }
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
    } else {
        step();
        step();
        step();
        have copied == owner->len by {
            assumption();
        }
        step();
        step();
        step();
        step();
        have 0 <= owner->len by {
            assumption();
        }
        have owner->cap == at(statement(9).entry, new_capacity) by {
            normalize();
        }
        have owner->len <= owner->cap by {
            assumption();
        }
        have 1 <= owner->cap by {
            assumption();
        }
        have owner->cap <= 536870911 by {
            assumption();
        }
        have separate(memory(object(owner)), memory(owner->data[0..owner->cap])) by {
            assumption();
        }
        have owner->len == old(owner->len) by {
            transport(old(owner->len) == old(owner->len), owner->len == old(owner->len)) using {
            }
            assumption();
        }
        have forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) } by simp;
        have loadable(owner->data[0..owner->len]) by {
            transport(forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) }, loadable(owner->data[0..owner->len])) using {
                forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) };
            }
            assumption();
        }
        fold(allocated_vector(owner));
        frame() using {
        }
        have result == 1 by {
            normalize();
        }
        have result == 0 or result == 1 by {
            normalize();
        }
        have owner->len == old(owner->len) by {
            normalize();
        }
        have result == 0 implies owner->cap == old(owner->cap) by {
            normalize();
        }
        have result == 0 implies owner->data == old(owner->data) by {
            normalize();
        }
        have result == 1 implies owner->cap == (old(owner->cap) + 1) by {
            normalize();
        }
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
    }
}

int32 vector_push(struct vector* owner, int32 value) {
    requires owner->len < owner->cap;
    owns vector_storage(owner);
    mutable owner->len, owner->data[owner->len..owner->len + 1];
    ensures result == old(owner->len) + 1;
    ensures owner->len == old(owner->len) + 1;
    ensures owner->data[old(owner->len)] == value;
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
    ensures forall (k: int32) {
        0 <= k and k < old(owner->len) implies
            owner->data[k] == old(owner->data[k])
    };
} by {
    unfold(vector_storage(owner));
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    fold(vector_storage(owner));
    have at(function.entry, owner->len) <= at(function.entry, owner->len) by {
        normalize();
    }
    have at(function.entry, owner->len) < at(function.entry, (owner->len + 1)) by {
        apply(int32_increment_strictly_increases(at(function.entry, owner->len), at(function.entry, owner->cap))) using {
            at(function.entry, owner->len) < at(function.entry, owner->cap);
        }
        assumption();
    }
    frame() using {
        at(statement(5).entry, owner->len) < at(statement(5).entry, owner->cap);
        at(function.entry, owner->len) <= at(function.entry, owner->len);
        at(function.entry, owner->len) < at(function.entry, (owner->len + 1));
    }
    have result == (old(owner->len) + 1) by {
        normalize();
    }
    have owner->len == (old(owner->len) + 1) by {
        normalize();
    }
    have owner->data[old(owner->len)] == value by {
        normalize();
    }
    have owner->cap == old(owner->cap) by {
        normalize();
    }
    have owner->data == old(owner->data) by {
        normalize();
    }
    have forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < old(owner->len));
        transport(old(owner->data[k]) == old(owner->data[k]), owner->data[k] == old(owner->data[k])) using {
            at(statement(5).entry, owner->len) <= at(statement(5).entry, owner->cap);
            0 <= k;
            k < old(owner->len);
        }
        assumption();
    }
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
}

int32 allocated_vector_push(struct vector* owner, int32 value) {
    requires owner->cap <= 536870910;
    consumes allocated_vector(owner);
    mutable owner->len, owner->cap, owner->data,
        owner->data[0..owner->cap];
    produces allocated_vector(owner);
    ensures result == 0 or result == 1;
    ensures result == 0 implies owner->len == old(owner->len);
    ensures result == 0 implies owner->cap == old(owner->cap);
    ensures result == 0 implies owner->data == old(owner->data);
    ensures result == 1 implies owner->len == old(owner->len) + 1;
    ensures result == 1 implies owner->data[old(owner->len)] == value;
    ensures forall (k: int32) {
        0 <= k and k < old(owner->len) implies
            owner->data[k] == old(owner->data[k])
    };
    ensures old(owner->len) < old(owner->cap) implies result == 1;
    ensures old(owner->len) < old(owner->cap) implies
        owner->cap == old(owner->cap);
    ensures old(owner->len) < old(owner->cap) implies
        owner->data == old(owner->data);
} by {
    if owner->len == owner->cap {
        open(allocated_vector(owner)) {
            step();
            step();
            step();
        }
        step();
        if c(grown) == 0 {
            step();
            step();
            have not old(owner->len) < old(owner->cap) by {
                rewrite(at(function.entry, owner->len == owner->cap));
                normalize();
            }
            frame() using {
            }
            have result == 0 by {
                normalize();
            }
            have result == 0 or result == 1 by {
                normalize();
            }
            have result == 0 implies owner->len == old(owner->len) by {
                intro();
                transport(old(owner->len) == old(owner->len), owner->len == old(owner->len)) using {
                }
                assumption();
            }
            have result == 0 implies owner->cap == old(owner->cap) by {
                intro();
                extract(at(statement(4).entry, owner->cap) == at(statement(3).entry, owner->cap));
                assumption();
            }
            have result == 0 implies owner->data == old(owner->data) by {
                intro();
                extract(at(statement(4).entry, owner->data) == at(statement(3).entry, owner->data));
                assumption();
            }
            have result == 1 implies owner->len == (old(owner->len) + 1) by {
                intro();
                contradiction(result == 1);
            }
            have result == 1 implies owner->data[old(owner->len)] == value by {
                intro();
                contradiction(result == 1);
            }
            have forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) } by {
                assumption();
            }
            have old(owner->len) < old(owner->cap) implies result == 1 by {
                intro();
                contradiction(old(owner->len) < old(owner->cap));
            }
            have old(owner->len) < old(owner->cap) implies owner->cap == old(owner->cap) by {
                intro();
                contradiction(old(owner->len) < old(owner->cap));
            }
            have old(owner->len) < old(owner->cap) implies owner->data == old(owner->data) by {
                intro();
                contradiction(old(owner->len) < old(owner->cap));
            }
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
        } else {
            step();
            step();
            unfold(allocated_vector(owner));
            have c(grown) == 1 by {
                cases (c(grown) == 0 or c(grown) == 1) {
                    contradiction(c(grown) == 0);
                } {
                    assumption();
                }
            }
            have owner->len == old(owner->len) by {
                assumption();
            }
            have owner->cap == (old(owner->cap) + 1) by {
                extract(owner->cap == (old(owner->cap) + 1));
                assumption();
            }
            have at(function.entry, owner->cap) <= 536870911 by {
                assumption();
            }
            have 536870911 < 2147483647 by {
                normalize();
            }
            apply(int32_le_lt_transitive(at(function.entry, owner->cap), 536870911, 2147483647)) using {
                at(function.entry, owner->cap) <= 536870911;
                536870911 < 2147483647;
            }
            apply(int32_increment_strictly_increases(at(function.entry, owner->cap), 2147483647)) using {
                at(function.entry, owner->cap) < 2147483647;
            }
            have owner->len < owner->cap by {
                rewrite(owner->cap == (old(owner->cap) + 1));
                rewrite(at(function.entry, owner->len == owner->cap));
                assumption();
            }
            fold(vector_storage(owner));
            step();
            have at(statement(8).exit, owner->data[at(statement(8).entry, owner->len)]) == at(statement(8).exit, value) by {
                assumption();
            }
            unfold(vector_storage(owner));
            have 0 <= owner->len by {
                assumption();
            }
            have owner->len <= owner->cap by {
                assumption();
            }
            have 1 <= owner->cap by {
                rewrite(owner->cap == at(statement(6).exit, owner->cap));
                assumption();
            }
            have owner->cap <= 536870911 by {
                rewrite(owner->cap == at(statement(6).exit, owner->cap));
                assumption();
            }
            fold(allocated_vector(owner));
            step();
            frame() using {
            }
            have not old(owner->len) < old(owner->cap) by {
                rewrite(at(function.entry, owner->len == owner->cap));
                normalize();
            }
            have result == 0 or result == 1 by {
                normalize();
            }
            have result == 0 implies owner->len == old(owner->len) by {
                normalize();
            }
            have result == 0 implies owner->cap == old(owner->cap) by {
                normalize();
            }
            have result == 0 implies owner->data == old(owner->data) by {
                normalize();
            }
            have result == 1 implies owner->len == (old(owner->len) + 1) by {
                intro();
                assumption();
            }
            have at(statement(8).entry, owner->len) < at(statement(8).entry, owner->cap) by {
                assumption();
            }
            have at(statement(8).entry, owner->len) == old(owner->len) by {
                assumption();
            }
            have owner->cap == at(statement(8).entry, owner->cap) by {
                assumption();
            }
            have old(owner->len) < owner->cap by {
                transport(at(statement(8).entry, owner->len) < at(statement(8).entry, owner->cap), old(owner->len) < owner->cap) using {
                    at(statement(8).entry, owner->len) < at(statement(8).entry, owner->cap);
                    at(statement(8).entry, owner->len) == old(owner->len);
                    owner->cap == at(statement(8).entry, owner->cap);
                }
                assumption();
            }
            have owner->data[old(owner->len)] == value by {
                assumption();
            }
            have result == 1 implies owner->data[old(owner->len)] == value by {
                intro();
                assumption();
            }
            have forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) } by {
                intro();
                intro();
                extract(0 <= k);
                extract(k < old(owner->len));
                instantiate(forall (j: int32) { 0 <= j and j < old(owner->len) implies at(statement(4).entry, owner->data[j]) == old(owner->data[j]) }, k) using {
                    0 <= k;
                    k < old(owner->len);
                }
                transport(at(statement(4).entry, owner->data[k]) == old(owner->data[k]), owner->data[k] == old(owner->data[k])) using {
                    at(statement(4).entry, owner->data[k]) == old(owner->data[k]);
                    0 <= k;
                    k < old(owner->len);
                }
                assumption();
            }
            have old(owner->len) < old(owner->cap) implies result == 1 by {
                intro();
                contradiction(old(owner->len) < old(owner->cap));
            }
            have old(owner->len) < old(owner->cap) implies owner->cap == old(owner->cap) by {
                intro();
                contradiction(old(owner->len) < old(owner->cap));
            }
            have old(owner->len) < old(owner->cap) implies owner->data == old(owner->data) by {
                intro();
                contradiction(old(owner->len) < old(owner->cap));
            }
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
        }
    } else {
        observe(allocated_vector(owner));
        have owner->len <= owner->cap by {
            assumption();
        }
        have not owner->len == owner->cap by {
            assumption();
        }
        have owner->len < owner->cap by {
            apply(int32_le_and_neq_implies_lt(owner->len, owner->cap)) using {
                owner->len <= owner->cap;
                not owner->len == owner->cap;
            }
            assumption();
        }
        have old(owner->len) < old(owner->cap) by {
            assumption();
        }
        step();
        step();
        step();
        step();
        unfold(allocated_vector(owner));
        fold(vector_storage(owner));
        step();
        unfold(vector_storage(owner));
        have 0 <= owner->len by {
            assumption();
        }
        have owner->len <= owner->cap by {
            assumption();
        }
        have 1 <= owner->cap by {
            rewrite(owner->cap == at(statement(0).entry, owner->cap));
            assumption();
        }
        have owner->cap <= 536870911 by {
            rewrite(owner->cap == at(statement(0).entry, owner->cap));
            assumption();
        }
        fold(allocated_vector(owner));
        step();
        have 0 == 0 by {
            normalize();
        }
        have at(statement(0).entry, 0) <= at(statement(0).entry, owner->len) by {
            assumption();
        }
        have at(statement(0).entry, (owner->len + 1)) <= at(statement(0).entry, owner->cap) by {
            have at(statement(0).entry, owner->len) < at(statement(0).entry, owner->cap) by {
                transport(owner->len < owner->cap, at(statement(0).entry, owner->len) < at(statement(0).entry, owner->cap)) using {
                    owner->len < owner->cap;
                }
                assumption();
            }
            apply(int32_increment_upper_bound(at(statement(0).entry, owner->len), at(statement(0).entry, owner->cap))) using {
                at(statement(0).entry, owner->len) < at(statement(0).entry, owner->cap);
            }
            assumption();
        }
        frame() using {
            at(statement(8).entry, owner->len) < at(statement(8).entry, owner->cap);
            not owner->len == owner->cap;
            at(statement(0).entry, separate(memory(owner->len), memory(owner->cap)));
            at(statement(0).entry, separate(memory(owner->len), memory(owner->data)));
            at(statement(0).entry, separate(memory(object(owner)), memory(owner->data[0..owner->cap])));
            at(statement(0).entry, separate(memory(owner->cap), memory(owner->data)));
            at(statement(0).entry, separate(memory(owner->len), allocation(owner->data, (owner->cap * 4))));
            at(statement(0).entry, separate(memory(owner->cap), allocation(owner->data, (owner->cap * 4))));
            at(statement(0).entry, separate(memory(owner->data), allocation(owner->data, (owner->cap * 4))));
            at(statement(0).entry, separate(allocation(owner->data, (owner->cap * 4)), memory(owner->data[0..owner->cap])));
            at(statement(0).entry, loadable(owner->len));
            at(statement(0).entry, loadable(owner->cap));
            at(statement(0).entry, loadable(owner->data));
            at(statement(0).entry, loadable(owner->data[0..owner->cap]));
            at(statement(0).entry, loadable(owner->data[0..owner->len]));
            at(statement(0).entry, owner->cap) <= at(statement(0).entry, 536870910);
            separate(memory(owner->len), memory(owner->data[0..owner->cap]));
            separate(memory(owner->cap), memory(owner->data[0..owner->cap]));
            separate(memory(owner->data), memory(owner->data[0..owner->cap]));
            contains(allocated_vector(owner), memory(owner->len));
            contains(allocated_vector(owner), memory(owner->cap));
            contains(allocated_vector(owner), memory(owner->data));
            contains(allocated_vector(owner), allocation(owner->data, (owner->cap * 4)));
            contains(allocated_vector(owner), memory(owner->data[0..owner->cap]));
            at(statement(0).entry, 0) <= at(statement(0).entry, owner->len);
            at(statement(0).entry, owner->len) <= at(statement(0).entry, owner->cap);
            at(statement(0).entry, 1) <= at(statement(0).entry, owner->cap);
            at(statement(0).entry, owner->cap) <= at(statement(0).entry, 536870911);
            0 == 0;
            at(statement(0).entry, 0) <= at(statement(0).entry, owner->len);
            at(statement(0).entry, (owner->len + 1)) <= at(statement(0).entry, owner->cap);
        }
        have result == 1 by {
            normalize();
        }
        have result == 0 or result == 1 by {
            normalize();
        }
        have result == 0 implies owner->len == old(owner->len) by {
            normalize();
        }
        have result == 0 implies owner->cap == old(owner->cap) by {
            normalize();
        }
        have result == 0 implies owner->data == old(owner->data) by {
            normalize();
        }
        have result == 1 implies owner->len == (old(owner->len) + 1) by {
            intro();
            assumption();
        }
        have owner->data[old(owner->len)] == value by {
            assumption();
        }
        have result == 1 implies owner->data[old(owner->len)] == value by {
            intro();
            assumption();
        }
        have forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) } by {
            assumption();
        }
        have owner->cap == old(owner->cap) by {
            assumption();
        }
        have owner->data == old(owner->data) by {
            assumption();
        }
        have old(owner->len) < old(owner->cap) implies result == 1 by {
            intro();
            assumption();
        }
        have old(owner->len) < old(owner->cap) implies owner->cap == old(owner->cap) by {
            intro();
            assumption();
        }
        have old(owner->len) < old(owner->cap) implies owner->data == old(owner->data) by {
            intro();
            assumption();
        }
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
    }
}

int32 vector_init(struct vector* owner, int32 data[], int32 capacity) {
    requires 1 <= capacity;
    consumes object(owner);
    consumes data[0..capacity];
    mutable owner->len, owner->cap, owner->data;
    produces empty_vector(owner);
    ensures result == 0;
    ensures owner->len == 0;
    ensures owner->cap == capacity;
    ensures owner->data == data;
} by {
    step();
    step();
    step();
    step();
    fold(empty_vector(owner));
    frame() using {
    }
    have result == 0 by {
        normalize();
    }
    have owner->len == 0 by {
        normalize();
    }
    have owner->cap == capacity by {
        normalize();
    }
    have owner->data == data by {
        normalize();
    }
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
}

int32 vector_len(struct vector* owner) {
    views nonempty_vector(owner);
    immutable by {
        step();
        frame() using {
        }
    }

    ensures result == owner->len by {
        step();
        have result == owner->len by {
            normalize();
        }
        assumption();
    }
}

int32 vector_get(struct vector* owner, int32 index) {
    requires 0 <= index;
    requires index < owner->len;
    views nonempty_vector(owner);
    immutable;

    ensures result == owner->data[index];
    ensures result == old(owner->data[index]);
} by {
    step();
    step();
    step();
    frame() using {
    }
    have result == owner->data[index] by {
        normalize();
    }
    assumption();
    have result == old(owner->data[index]) by {
        assumption();
    }
    assumption();
}

int32 vector_set(struct vector* owner, int32 index, int32 value) {
    requires 0 <= index;
    requires index < owner->len;
    mutable owner->data[index..index + 1];
    owns nonempty_vector(owner);
    ensures result == value;
    ensures owner->data[index] == value;
    ensures owner->len == old(owner->len);
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
} by {
    unfold(nonempty_vector(owner));
    step();
    step();
    step();
    step();
    fold(nonempty_vector(owner));
    have index < (index + 1) by {
        apply(int32_increment_strictly_increases(at(statement(3).entry, index), at(statement(3).entry, owner->len))) using {
            at(statement(3).entry, index) < at(statement(3).entry, owner->len);
        }
        assumption();
    }
    have index <= index by {
        normalize();
    }
    have index < (index + 1) by {
        apply(int32_increment_strictly_increases(at(statement(3).entry, index), at(statement(3).entry, owner->len))) using {
            at(statement(3).entry, index) < at(statement(3).entry, owner->len);
        }
        assumption();
    }
    frame() using {
        at(statement(3).entry, 0) <= at(statement(3).entry, index);
        at(statement(3).entry, index) < at(statement(3).entry, owner->len);
        index <= index;
        index < (index + 1);
    }
    have result == value by {
        normalize();
    }
    have owner->data[index] == value by {
        normalize();
    }
    have owner->len == old(owner->len) by {
        normalize();
    }
    have owner->cap == old(owner->cap) by {
        normalize();
    }
    have owner->data == old(owner->data) by {
        normalize();
    }
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
}

int32 vector_fill(struct vector* owner, int32 value) {
    owns nonempty_vector(owner);
    mutable owner->data[0..owner->len];
    ensures result == owner->len;
} by {
    unfold(nonempty_vector(owner));
    step();
    step();
    have loadable(owner->len) by {
        transport(loadable(old(owner->len)), loadable(owner->len)) using {
            loadable(old(owner->len));
        }
        assumption();
    }
    have loadable(owner->cap) by {
        transport(loadable(old(owner->cap)), loadable(owner->cap)) using {
            loadable(old(owner->cap));
        }
        assumption();
    }
    have loadable(owner->data) by {
        transport(loadable(old(owner->data)), loadable(owner->data)) using {
            loadable(old(owner->data));
        }
        assumption();
    }
    have loadable(owner->data[0..owner->cap]) by {
        transport(loadable(old(owner->data[0..owner->cap])), loadable(owner->data[0..owner->cap])) using {
            loadable(old(owner->data[0..owner->cap]));
        }
        assumption();
    }
    have i >= 0 by {
        normalize();
    }
    have i <= owner->len by {
        apply(int32_positive_is_nonnegative(owner->len)) using {
            1 <= owner->len;
        }
        assumption();
    }
    loop as fill_cells {
        invariant i >= 0 and i <= owner->len;
        mutable owner->data[0..owner->len] by frame;
        initialize by {
            have i >= 0 and i <= owner->len by {
                have i >= 0 by {
                    normalize();
                }
                have i <= owner->len by {
                    assumption();
                }
                split();
            }
        }
        preserve by {
            have i < owner->cap by {
                apply(int32_lt_le_transitive(i, owner->len, owner->cap)) using {
                    i < owner->len;
                    owner->len <= owner->cap;
                }
                assumption();
            }
            step();
            step();
            have i >= 0 by {
                extract(at(statement(3).entry, i) >= 0);
                apply(int32_increment_greater_equal_lower_bound(at(statement(3).entry, i), 0, at(statement(3).entry, owner->len))) using {
                    at(statement(3).entry, i) >= 0;
                    at(statement(3).entry, i) < at(statement(3).entry, owner->len);
                }
                assumption();
            }
            have i <= owner->len by {
                apply(int32_increment_upper_bound(at(statement(3).entry, i), at(statement(3).entry, owner->len))) using {
                    at(statement(3).entry, i) < at(statement(3).entry, owner->len);
                }
                assumption();
            }
            close_invariants();
        }
    }
    step();
    frame() using {
    }
    fold(nonempty_vector(owner));
    assumption();
    have result == owner->len by {
        normalize();
    }
    assumption();
}

int32 vector_replace_if(
    struct vector* owner,
    int32 index,
    int32 replacement,
    int32 replace
) {
    requires 0 <= index;
    requires index < owner->len;
    owns nonempty_vector(owner);
    mutable owner->data[index..index + 1];

    ensures replace != 0 implies result == replacement;
} by {
    step();
    step();
    step();
    have replace == replace by {
        normalize();
    }
    branch {
        then {
            step();
            have replace != 0 implies selected == replacement by {
                rewrite(selected == replacement);
                normalize();
            }
            have not replace != 0 implies selected == original by {
                intro();
                contradiction(replace != 0);
            }
            have index < (index + 1) by {
                apply(int32_increment_strictly_increases(at(statement(4).entry, index), at(statement(4).entry, owner->len))) using {
                    at(statement(4).entry, index) < at(statement(4).entry, owner->len);
                }
                assumption();
            }
        }
        else {
            step();
            have replace != 0 implies selected == replacement by {
                have not replace != 0 by {
                    assumption();
                }
                intro();
                contradiction(not replace != 0);
            }
            have not replace != 0 implies selected == original by {
                intro();
                assumption();
            }
            have index < (index + 1) by {
                apply(int32_increment_strictly_increases(at(statement(5).entry, index), at(statement(5).entry, owner->len))) using {
                    at(statement(5).entry, index) < at(statement(5).entry, owner->len);
                }
                assumption();
            }
        }
    }
    step();
    have index < (index + 1) by {
        assumption();
    }
    frame() using {
    }
    have replace != 0 implies result == replacement by {
        assumption();
    }
    assumption();
    assumption();
}

int32 vector_clear(struct vector* owner) {
    consumes nonempty_vector(owner);
    mutable owner->len;
    produces empty_vector(owner);
    ensures result == 0;
    ensures owner->len == 0;
} by {
    unfold(nonempty_vector(owner));
    step();
    step();
    have owner->len == 0 by {
        normalize();
    }
    apply(int32_le_transitive(1, at(statement(0).entry, owner->len), at(statement(0).entry, owner->cap))) using {
        at(statement(0).entry, 1) <= at(statement(0).entry, owner->len);
        at(statement(0).entry, owner->len) <= at(statement(0).entry, owner->cap);
    }
    transport(at(statement(0).entry, 1) <= at(statement(0).entry, owner->cap), 1 <= owner->cap) using {
        at(statement(0).entry, 1) <= at(statement(0).entry, owner->cap);
    }
    assumption();
    have separate(memory(object(owner)), memory(owner->data[0..owner->cap])) by {
        assumption();
    }
    fold(empty_vector(owner));
    frame() using {
    }
    have owner->len == 0 by {
        normalize();
    }
    assumption();
    assumption();
}

int32 vector_pipeline(
    struct vector* owner,
    int32 data[],
    int32 capacity,
    int32 first,
    int32 replacement
) {
    requires 1 <= capacity;
    consumes object(owner);
    consumes data[0..capacity];

    produces empty_vector(owner);
    ensures result == replacement;
} by {
    step();
    step();
    step();
    have observed == 0 by {
        assumption();
    }
    have owner->len == 0 by {
        assumption();
    }
    have owner->cap == capacity by {
        assumption();
    }
    unfold(empty_vector(owner));
    have 0 <= owner->len by {
        rewrite(owner->len == 0);
        normalize();
    }
    have owner->len <= owner->cap by {
        rewrite(owner->len == 0);
        apply(int32_positive_is_nonnegative(owner->cap)) using {
            1 <= owner->cap;
        }
        assumption();
    }
    have loadable(owner->data[0..owner->len]) by {
        rewrite(owner->len == 0);
        normalize();
    }
    fold(vector_storage(owner));
    have owner->len < owner->cap by {
        rewrite(owner->len == 0);
        apply(int32_successor_le_implies_lt(0, owner->cap)) using {
            1 <= owner->cap;
        }
        assumption();
    }
    step();
    unfold(vector_storage(owner));
    have owner->len == 1 by {
        rewrite(owner->len == at(statement(2).exit, (owner->len + 1)));
        rewrite(at(statement(2).exit, owner->len) == at(statement(2).exit, 0));
        normalize();
    }
    have 1 <= owner->len by {
        rewrite(owner->len == 1);
        normalize();
    }
    fold(nonempty_vector(owner));
    have 0 < owner->len by {
        rewrite(owner->len == 1);
        normalize();
    }
    step();
    have owner->len == 1 by {
        rewrite(at(statement(3).exit, 1) == at(statement(3).exit, owner->len));
        normalize();
    }
    have 0 < owner->len by {
        rewrite(owner->len == 1);
        normalize();
    }
    step();
    have owner->len == 1 by {
        rewrite(at(statement(3).exit, 1) == at(statement(3).exit, owner->len));
        assumption();
    }
    observe(nonempty_vector(owner));
    have owner->data[0] == replacement by {
        assumption();
    }
    have 0 < owner->len by {
        rewrite(owner->len == 1);
        normalize();
    }
    step();
    have observed == owner->data[0] by {
        assumption();
    }
    apply(int32_equality_transitive(observed, owner->data[0], replacement)) using {
        observed == owner->data[0];
        owner->data[0] == replacement;
    }
    step();
    step();
    have result == replacement by {
        assumption();
    }
    assumption();
    assumption();
}
