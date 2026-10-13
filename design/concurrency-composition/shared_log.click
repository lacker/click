target "x86_64-linux-userspace";
runtime "modeled-pthread";

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
    fact owner->cap <= 1073741823;
    fact separate(memory(*owner), memory(owner->data[0..owner->cap]));
}

resource nonempty_vector(owner: struct vector*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 1 <= owner->len;
    fact owner->len <= owner->cap;
    fact owner->cap <= 1073741823;
    fact separate(memory(*owner), memory(owner->data[0..owner->cap]));
}

resource vector_storage(owner: struct vector*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
    fact owner->cap <= 1073741823;
    fact separate(memory(*owner), memory(owner->data[0..owner->cap]));
}

resource allocated_vector(owner: struct vector*) {
    field cap: int32;
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns allocation(owner->data, owner->cap * 4);
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
    fact 1 <= owner->cap;
    fact owner->cap <= 536870911;
    fact owner->cap == cap;
    fact separate(memory(*owner), memory(owner->data[0..owner->cap]));
}

verifying "vector_copy.c";
verifying "vector_grow.c";
verifying "vector_push.c";
verifying "allocated_vector_push.c";
verifying "shared_log.c";

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
    requires ((uint32)length) <= 1073741823u32;
    requires ((uint32)dst_capacity) <= 1073741823u32;
    requires ((uint32)src_capacity) <= 1073741823u32;
    owns dst[0..dst_capacity];
    views src[0..src_capacity];
    requires separate(memory(dst[0..dst_capacity]), memory(src[0..src_capacity]));
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
        decreases length - i;
        invariant 0 <= i;
        invariant i <= length;
        invariant forall (k: int32) { 0 <= k and k < i implies dst[k] == old(src[k]) };
        owns dst[0..length];
        initialize by {
            have 0 <= i by {
                normalize();
            }
            have i <= length by {
                assumption();
            }
            have forall (k: int32) { 0 <= k and k < i implies dst[k] == old(src[k]) } by {
                intro();
                intro();
                extract(0 <= k);
                extract(k < i);
                have i == 0 by {
                    normalize();
                }
                have not (0 <= k) by {
                    arithmetic() using {
                        k < i;
                        i == 0;
                    }
                }
                contradiction(0 <= k);
            }
        }
        preserve by {
            step();
            step();
            simp();
        }
    }
    have i == length by {
        apply(int32_less_equal_and_not_less_than_implies_equal(at(loop(0).exit, i), at(loop(0).exit, length))) using {
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
    consumes before: allocated_vector(owner);
    produces after: allocated_vector(owner);
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
    unfold(before);
    have owner->cap < 2147483647 by {
        apply(int32_less_equal_less_than_transitive(owner->cap, 536870910, 2147483647)) using {
            owner->cap <= 536870910;
        }
        assumption();
    }
    have (owner->cap + 1) <= 536870911 by {
        apply(int32_less_equal_less_than_transitive(owner->cap, 536870910, 536870911)) using {
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
    have 0 <= new_capacity by {
        apply(int32_less_equal_transitive(0, 1, new_capacity)) using {
            1 <= new_capacity;
        }
        assumption();
    }
    have 0 <= old_capacity by {
        have old_capacity == owner->cap by {
            normalize();
        }
        rewrite(old_capacity == owner->cap);
        apply(int32_less_equal_transitive(0, 1, owner->cap)) using {
            1 <= owner->cap;
        }
        assumption();
    }
    have ((uint32)new_capacity) <= 1073741823u32 by {
        arithmetic() using {
            0 <= new_capacity;
            new_capacity <= 536870911;
        }
    }
    have ((uint32)old_capacity) <= 1073741823u32 by {
        have old_capacity == owner->cap by {
            normalize();
        }
        rewrite(old_capacity == owner->cap);
        arithmetic() using {
            1 <= owner->cap;
            owner->cap <= 536870910;
        }
    }
    have owner->len <= 536870910 by {
        apply(int32_less_equal_transitive(owner->len, owner->cap, 536870910)) using {
            owner->len <= owner->cap;
            owner->cap <= 536870910;
        }
        assumption();
    }
    have ((uint32)owner->len) <= 1073741823u32 by {
        arithmetic() using {
            0 <= owner->len;
            owner->len <= 536870910;
        }
    }
    if new_data == 0 {
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
        let after = fold(allocated_vector(owner), { cap: owner->cap });
        have result == 0 by {
            normalize();
        }
        have result == 0 or result == 1 by {
            assumption();
        }
        have owner->len == old(owner->len) by {
            normalize();
        }
        have result == 0 implies owner->cap == old(owner->cap) by {
            simp();
        }
        have result == 0 implies owner->data == old(owner->data) by {
            simp();
        }
        have result == 1 implies owner->cap == (old(owner->cap) + 1) by {
            simp();
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
        have separate(memory(*owner), memory(owner->data[0..owner->cap])) by {
            assumption();
        }
        have owner->len == old(owner->len) by {
            transport(old(owner->len) == old(owner->len), owner->len == old(owner->len)) using {
            }
            assumption();
        }
        have forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) } by simp;
        let after = fold(allocated_vector(owner), { cap: owner->cap });
        have result == 1 by {
            normalize();
        }
        have result == 0 or result == 1 by {
            assumption();
        }
        have owner->len == old(owner->len) by {
            normalize();
        }
        have result == 0 implies owner->cap == old(owner->cap) by {
            simp();
        }
        have result == 0 implies owner->data == old(owner->data) by {
            simp();
        }
        have result == 1 implies owner->cap == (old(owner->cap) + 1) by {
            simp();
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
    consumes before: allocated_vector(owner);
    produces after: allocated_vector(owner);
    ensures result == 0 or result == 1;
    ensures result == 0 implies owner->len == old(owner->len);
    ensures result == 0 implies owner->cap == old(owner->cap);
    ensures result == 0 implies owner->data == old(owner->data);
    ensures owner->cap <= old(owner->cap) + 1;
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
        unfold(before);
        step();
        step();
        step();
        let ready = fold(allocated_vector(owner), { cap: owner->cap });
        let { after: after } = step(vector_grow(owner), { before: ready });
        if c(grown) == 0 {
            step();
            step();
            have not old(owner->len) < old(owner->cap) by {
                rewrite(at(function.entry, owner->len == owner->cap));
                normalize();
            }
            have result == 0 by {
                normalize();
            }
            have result == 0 or result == 1 by {
                assumption();
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
            have owner->cap == old(owner->cap) by {
                extract(at(statement(4).entry, owner->cap) == at(statement(3).entry, owner->cap));
                assumption();
            }
            have owner->cap <= old(owner->cap) by {
                rewrite(owner->cap == old(owner->cap));
                normalize();
            }
            have old(owner->cap) <= 536870910;
            have 536870910 < 2147483647 by normalize();
            have old(owner->cap) < 2147483647 by apply(int32_less_equal_less_than_transitive(old(owner->cap), 536870910, 2147483647)) using {
                old(owner->cap) <= 536870910;
                536870910 < 2147483647;
            }
            have owner->cap <= old(owner->cap) + 1 by apply(int32_increment_lower_bound(old(owner->cap), owner->cap, 2147483647)) using {
                owner->cap <= old(owner->cap);
                old(owner->cap) < 2147483647;
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
            assumption();
        } else {
            step();
            step();
            unfold(after);
            have c(grown) == 1 by {
                cases {
                    c(grown) == 0 => {
                        contradiction(c(grown) == 0);
                    }
                    c(grown) == 1 => {
                        assumption();
                    }
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
            apply(int32_less_equal_less_than_transitive(at(function.entry, owner->cap), 536870911, 2147483647)) using {
                at(function.entry, owner->cap) <= 536870911;
                536870911 < 2147483647;
            }
            apply(int32_increment_strictly_increases(at(function.entry, owner->cap), 2147483647)) using {
                at(function.entry, owner->cap) < 2147483647;
            }
            have owner->len < owner->cap by {
                rewrite(owner->len == old(owner->len));
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
            have owner->cap == at(statement(8).entry, owner->cap) by {
                assumption();
            }
            have 1 <= at(statement(8).entry, owner->cap) by {
                assumption();
            }
            have at(statement(8).entry, owner->cap) <= 536870911 by {
                assumption();
            }
            have 1 <= owner->cap by {
                rewrite(owner->cap == at(statement(8).entry, owner->cap));
                assumption();
            }
            have owner->cap <= 536870911 by {
                rewrite(owner->cap == at(statement(8).entry, owner->cap));
                assumption();
            }
            let after = fold(allocated_vector(owner), { cap: owner->cap });
            step();
            have not old(owner->len) < old(owner->cap) by {
                rewrite(at(function.entry, owner->len == owner->cap));
                normalize();
            }
            have result == 0 or result == 1 by {
                have result == 1 by normalize();
                assumption();
            }
            have result == 0 implies owner->len == old(owner->len) by {
                simp();
            }
            have result == 0 implies owner->cap == old(owner->cap) by {
                simp();
            }
            have result == 0 implies owner->data == old(owner->data) by {
                simp();
            }
            have at(statement(8).entry, owner->len) == old(owner->len) by {
                assumption();
            }
            have owner->len == (old(owner->len) + 1) by {
                rewrite(owner->len == (at(statement(8).entry, owner->len) + 1));
                rewrite(at(statement(8).entry, owner->len) == old(owner->len));
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
                rewrite(old(owner->len) == at(statement(8).entry, owner->len));
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
                instantiate(forall (j: int32) { 0 <= j and j < old(owner->len) implies at(statement(4).entry, owner->data[j]) == old(owner->data[j]) }, k);
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
            have owner->cap == old(owner->cap) + 1 by {
                rewrite(owner->cap == at(statement(8).entry, owner->cap));
                assumption();
            }
            have owner->cap <= old(owner->cap) + 1 by {
                rewrite(owner->cap == old(owner->cap) + 1);
                normalize();
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
            assumption();
        }
    } else {
        unfold(before);
        have owner->len <= owner->cap by {
            assumption();
        }
        have not owner->len == owner->cap by {
            assumption();
        }
        have owner->len < owner->cap by {
            apply(int32_less_equal_and_not_equal_implies_less_than(owner->len, owner->cap)) using {
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
        let after = fold(allocated_vector(owner), { cap: owner->cap });
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
        have result == 1 by {
            normalize();
        }
        have result == 0 or result == 1 by {
            assumption();
        }
        have result == 0 implies owner->len == old(owner->len) by {
            simp();
        }
        have result == 0 implies owner->cap == old(owner->cap) by {
            simp();
        }
        have result == 0 implies owner->data == old(owner->data) by {
            simp();
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
        have owner->cap <= old(owner->cap) by {
            rewrite(owner->cap == old(owner->cap));
            normalize();
        }
        have old(owner->cap) <= 536870910;
        have 536870910 < 2147483647 by normalize();
        have old(owner->cap) < 2147483647 by apply(int32_less_equal_less_than_transitive(old(owner->cap), 536870910, 2147483647)) using {
            old(owner->cap) <= 536870910;
            536870910 < 2147483647;
        }
        have owner->cap <= old(owner->cap) + 1 by apply(int32_increment_lower_bound(old(owner->cap), owner->cap, 2147483647)) using {
            owner->cap <= old(owner->cap);
            old(owner->cap) < 2147483647;
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
        assumption();
    }
}

// Each producer still to run holds one credit. The log's control owns the
// vector, whose allocation and data range change when a push grows it, and
// the credit authority; its fact keeps room for every remaining push.
authorized resource credit(log: struct shared_log*) {}

resource log_state(log: struct shared_log*) {
    field cap: int32;
    field slack: int32;
    owns log->items;
    owns items: allocated_vector(log->items);
    owns authority(credit(log));
    fact items.cap == cap;
    fact slack == count(credit(log));
    fact 0 <= slack;
    fact to_integer(cap) + to_integer(slack) <= 536870910;
}

void* producer(void* argument) {
    owns access: mutex_use(
        &((struct shared_log*)argument)->mu,
        log_state((struct shared_log*)argument)
    );
    consumes credit((struct shared_log*)argument);
    ensures result == 0;
} by {
    step();
    step();
    let { guard: guard, state: state } = step(
        pthread_mutex_lock(&log->mu), { access: access }
    );
    let { cap: cap, slack: slack, items: items } = unfold(state);
    have count(credit(log)) >= 1;
    have slack == count(credit(log));
    have 1 <= slack;
    unfold(credit(log));
    have to_integer(1) <= to_integer(slack) by apply(int32_less_equal_to_integer(1, slack));
    have to_integer(cap) <= to_integer(536870909) by arithmetic() using {
        to_integer(cap) + to_integer(slack) <= 536870910;
        to_integer(1) <= to_integer(slack);
        to_integer(1) == 1;
        to_integer(536870909) == 536870909;
    };
    have cap <= 536870909 by apply(int32_to_integer_less_equal_implies_less_equal(cap, 536870909));
    have items.cap == cap;
    let { cap: items_cap } = unfold(items);
    have log->items->cap == items_cap;
    have log->items->cap == cap;
    have log->items->cap <= 536870910;
    let ready = fold(allocated_vector(log->items), { cap: log->items->cap });
    let { after: after } = step(allocated_vector_push(log->items, 7), { before: ready });
    let { cap: pushed_cap } = unfold(after);
    have log->items->cap <= at(statement(3).entry, log->items->cap) + 1;
    have at(statement(3).entry, log->items->cap) == cap;
    have log->items->cap == pushed_cap;
    have pushed_cap == log->items->cap;
    have cap == at(statement(3).entry, log->items->cap);
    have pushed_cap <= cap + 1 by {
        rewrite(pushed_cap == log->items->cap);
        rewrite(cap == at(statement(3).entry, log->items->cap));
        assumption();
    }
    have defined(cap + 1);
    have defined(slack - 1);
    have to_integer(cap + 1) == to_integer(cap) + to_integer(1) by apply(int32_add_to_integer(cap, 1));
    have to_integer(slack - 1) == to_integer(slack) - to_integer(1) by apply(int32_subtract_to_integer(slack, 1));
    have to_integer(pushed_cap) <= to_integer(cap + 1) by apply(int32_less_equal_to_integer(pushed_cap, cap + 1));
    have to_integer(pushed_cap) + to_integer(slack - 1) <= 536870910 by arithmetic() using {
        to_integer(pushed_cap) <= to_integer(cap + 1);
        to_integer(cap + 1) == to_integer(cap) + to_integer(1);
        to_integer(slack - 1) == to_integer(slack) - to_integer(1);
        to_integer(cap) + to_integer(slack) <= 536870910;
    };
    let pushed = fold(allocated_vector(log->items), { cap: log->items->cap });
    let restored = fold(log_state(log), { cap: pushed_cap, slack: slack - 1 }, { items: pushed });
    step(pthread_mutex_unlock(&log->mu), {
        access: access, guard: guard, state: restored
    });
    step();
    simp();
}

int32 run_two_producers(struct shared_log* log) {
    owns log->mu;
    requires aligned(&log->mu, 8);
    owns log->items;
    consumes before: allocated_vector(log->items);
    produces after: allocated_vector(log->items);
    owns authority(credit(log));
    requires count(credit(log)) == 0;
    requires before.cap <= 536870908;
    ensures result == 0 or result == 1;
} by {
    step();
    step();
    fold(credit(log));
    fold(credit(log));
    have to_integer(before.cap) <= to_integer(536870908) by apply(int32_less_equal_to_integer(before.cap, 536870908));
    have to_integer(before.cap) + to_integer(2) <= 536870910 by arithmetic() using {
        to_integer(before.cap) <= to_integer(536870908);
        to_integer(536870908) == 536870908;
        to_integer(2) == 2;
    };
    let state = fold(log_state(log), { cap: before.cap, slack: 2 }, { items: before });
    let { lifetime: lifetime } = step(pthread_mutex_init(&log->mu, 0), { state: state });
    branch then {
        let { cap: cap1, slack: slack1, items: after } = unfold(state);
        unfold(credit(log));
        unfold(credit(log));
        step();
        simp();
    } else {}
    step();
    branch then {
        step(pthread_mutex_destroy(&log->mu), { lifetime: lifetime });
        let { cap: cap2, slack: slack2, items: after } = unfold(state);
        unfold(credit(log));
        unfold(credit(log));
        step();
        simp();
    } else {}
    step();
    branch then {
        step();
        step(pthread_mutex_destroy(&log->mu), { lifetime: lifetime });
        let { cap: cap3, slack: slack3, items: after } = unfold(state);
        unfold(credit(log));
        step();
        simp();
    } else {}
    step();
    step();
    step(pthread_mutex_destroy(&log->mu), { lifetime: lifetime });
    let { cap: cap4, slack: slack4, items: after } = unfold(state);
    step();
    simp();
}
