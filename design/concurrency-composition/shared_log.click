import click::separation;
import click::integer;

target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";

theorem int32_equality_transitive(first: int32, second: int32, third: int32) {
    requires first == second;
    requires second == third;

    ensures first == third by {
        close();
    }
}

theorem vector_nonnegative_as_uint32_bound(value: int32, limit: uint32) {
    requires 0 <= to_integer(value);
    requires to_integer(value) <= to_integer(limit);
    ensures (value as uint32) <= limit by {
        have to_integer(value) <= 2147483647;
        have to_integer(value as uint32) == to_integer(value) by {
            close() using { 0 <= to_integer(value); to_integer(value) <= 2147483647; };
        }
        have to_integer(value as uint32) <= to_integer(limit) by {
            rewrite(to_integer(value as uint32), to_integer(value));
            close();
        }
        apply(click::integer::uint32_to_integer_less_equal_implies_less_equal(value as uint32, limit));
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

theorem selected_array_cell(whole: Resource, kept: Resource, p: int32*, len: int32, i: int32) {
    requires separate(whole, memory(p[0..len]));
    requires contains(whole, kept);
    requires 0 <= i;
    requires i < len;
    ensures separate(kept, memory(p[i])) by {
        have contains(memory(p[0..len]), memory(p[i])) by {
            apply(separation::contains_element(p, 0, len, i));
        }
        apply(separation::separate_restrict(whole, memory(p[0..len]), kept, memory(p[i])));
    }
}

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
    requires (length as uint32) <= 1073741823u32;
    requires (dst_capacity as uint32) <= 1073741823u32;
    requires (src_capacity as uint32) <= 1073741823u32;
    owns uninitialized(dst[0..dst_capacity]);
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
    have contains(memory(dst[0..dst_capacity]), memory(dst[0..length])) by {
        apply(separation::contains_subrange(dst, 0, dst_capacity, 0, length));
    }
    have contains(memory(src[0..src_capacity]), memory(src[0..src_capacity])) by { apply(click::separation::contains_refl(memory(src[0..src_capacity]))); }
    have separate(memory(dst[0..length]), memory(src[0..src_capacity])) by {
        apply(separation::separate_restrict(memory(dst[0..dst_capacity]), memory(src[0..src_capacity]), memory(dst[0..length]), memory(src[0..src_capacity])));
    }
    loop {
        decreases length - i;
        invariant forall (k: int32) { 0 <= k and k < length implies src[k] == old(src[k]) };
        invariant 0 <= i;
        invariant i <= length;
        invariant forall (k: int32) { 0 <= k and k < i implies dst[k] == old(src[k]) };
        owns dst[0..length];
        initialize by {
            have forall (k: int32) { 0 <= k and k < length implies src[k] == old(src[k]) } by {
                intro() {
                    intro() {
                        close();
                    }
                }
            }
            have 0 <= i;
            have i <= length;
            have forall (k: int32) { 0 <= k and k < i implies dst[k] == old(src[k]) } by {
                intro() {
                    intro() {
                        have 0 <= k;
                        have k < i;
                        close();
                    }
                }
            }
        }
        maintain by {
            have i < dst_capacity by { close(); }
            have contains(memory(dst[0..dst_capacity]), memory(dst[i])) by {
                apply(separation::contains_element(dst, 0, dst_capacity, i));
            }
            apply(separation::separate_restrict(
                memory(dst[0..dst_capacity]), memory(src[0..src_capacity]),
                memory(dst[i]), memory(src[0..src_capacity])));
            step();
            // Establish the source frame before incrementing the write index.
            have forall (k: int32) { 0 <= k and k < length implies src[k] == old(src[k]) } by {
                intro() {
                    intro() {
                        have at(region(3).entry, 0) <= at(region(3).entry, k) and at(region(3).entry, k) < at(region(3).entry, length);
                        instantiate(forall (k: int32) { at(region(3).entry, 0) <= at(region(3).entry, k) and at(region(3).entry, k) < at(region(3).entry, length) implies at(region(3).entry, src[k]) == old(src[k]) }, k);
                        have at(region(3).entry, src[k]) == src[k] by {
                            have k < src_capacity by { close() using { k < length; length <= src_capacity; }; }
                            have contains(memory(dst[i]), memory(dst[i])) by { apply(click::separation::contains_refl(memory(dst[i]))); }
                            have contains(memory(src[0..src_capacity]), memory(src[k])) by {
                                apply(separation::contains_element(src, 0, src_capacity, k));
                            }
                            have separate(memory(dst[i]), memory(src[k])) by {
                                apply(separation::separate_restrict(memory(dst[i]), memory(src[0..src_capacity]), memory(dst[i]), memory(src[k])));
                            }
                            have separate(loop(0).statement(0).footprint, memory(src[k])) by {
                                close() using { separate(memory(dst[i]), memory(src[k])); };
                            }
                            have at(loop(0).statement(0).exit, src[k]) == at(loop(0).statement(0).entry, src[k]) by {
                                preserve(memory(src[k]), loop(0).statement(0));
                            }
                            close();
                        }
                        have src[k] == at(region(3).entry, src[k]) by {
                            rewrite(at(region(3).entry, src[k]), src[k]);
                            close();
                        }
                        rewrite(src[k], at(region(3).entry, src[k]));
                        close();
                    }
                }
            }
            step();
            have 0 <= i by {
                close() using { (at(region(3).entry, 0) as int32) <= (at(region(3).entry, i) as int32); (at(region(3).entry, i) as int32) < (at(region(3).entry, length) as int32); };
            }
            have i <= length by {
                close() using { (at(region(3).entry, i) as int32) < (at(region(3).entry, length) as int32); };
            }
            have forall (k: int32) { 0 <= k and k < i implies dst[k] == old(src[k]) } by {
                intro() {
                    intro() {
                        have 0 <= k;
                        have k < i;
                        if at(region(4).entry, k) < at(region(4).entry, (i as int32)) {
                            have at(region(4).entry, k) != at(region(4).entry, (i as int32)) by {
                                have at(region(4).entry, k) < at(region(4).entry, (i as int32)) by {
                                    close();
                                }
                                if at(region(4).entry, k) == at(region(4).entry, (i as int32)) {
                                    have false by {
                                        close() using { at(region(4).entry, k) < at(region(4).entry, (i as int32)); at(region(4).entry, k) == at(region(4).entry, (i as int32)); };
                                    }
                                    close();
                                } else {
                                    close();
                                }
                            }
                            have 0 <= k and k < i;
                            instantiate(at(region(3).entry, forall (k: int32) { 0 <= k and k < i implies dst[k] == old(src[k]) }), k);
                            have at(region(3).entry, separate(memory(dst[k]), memory(dst[i]))) by {
                                apply(separation::separate_elements(dst, k, at(region(3).entry, i)));
                            }
                            have separate(loop(0).statement(0).footprint, memory(dst[k])) by {
                                close() using { at(region(3).entry, separate(memory(dst[k]), memory(dst[i]))); };
                            }
                            have at(loop(0).statement(0).exit, dst[k]) == at(loop(0).statement(0).entry, dst[k]) by {
                                preserve(memory(dst[k]), loop(0).statement(0));
                            }
                            close();
                        } else {
                            have at(region(4).entry, k) == at(region(4).entry, (i as int32)) by {
                                have at(region(4).entry, k) <= at(region(4).entry, (i as int32)) by {
                                    close() using { (at(region(3).entry, i) as int32) < (at(region(3).entry, length) as
                                            int32); (k as int32) < (i as int32); (at(region(3).entry, 0) as int32) <= (at(region(3).entry, i) as
                                            int32); (at(function.entry, length) as int32) <= (at(function.entry,
                                            dst_capacity) as int32); (at(function.entry, dst_capacity) as int32) <= (at(function.entry,
                                            1073741823) as int32); (at(function.entry, i) as int32) <= (at(function.entry, length) as
                                            int32); };
                                }
                                close() using { at(region(4).entry, k) <= at(region(4).entry, (i as int32)); not k < at(region(3).entry, i); };
                            }
                            rewrite(at(region(4).entry, k), at(region(4).entry, (i as int32)));
                            have 0 <= k and k < length;
                            instantiate(forall (k: int32) { 0 <= k and k < length implies src[k] == old(src[k]) }, k);
                            have 0 <= (at(region(3).entry, i)) and (at(region(3).entry, i)) < length;
                            instantiate(at(region(3).entry, forall (k: int32) { 0 <= k and k < length implies src[k] == old(src[k]) }), at(region(3).entry, i));
                            close();
                        }
                    }
                }
            }
            have forall (k: int32) { 0 <= k and k < length implies src[k] == old(src[k]) } implies 0 <= i by {
                intro() {
                    close();
                }
            }
            have forall (k: int32) { 0 <= k and k < length implies src[k] == old(src[k]) } implies 0 <= i implies i <= length by {
                intro() {
                    intro() {
                        close();
                    }
                }
            }
            have forall (k: int32) { 0 <= k and k < length implies src[k] == old(src[k]) } implies 0 <= i implies i <= length implies forall (k: int32) { 0 <= k and k < i implies dst[k] == old(src[k]) } by {
                intro() {
                    intro() {
                        intro() {
                            close();
                        }
                    }
                }
            }
            have (let integer_value: Integer = 0; integer_value) <= (to_integer((length as int32)) - to_integer((i as int32))) by {
                close() using { to_integer((i as int32)) <= to_integer((length as int32)); };
            }
            have (let integer_value: Integer = (to_integer((length as int32)) - to_integer((i as int32))); integer_value) < (to_integer((length as int32)) - to_integer(at(region(3).entry, (i as int32)))) by {
                have -2147483648 <= (to_integer(at(region(3).entry, (i as int32))) + 1) by {
                    close() using { 0 <= to_integer(at(region(3).entry, (i as int32))); };
                }
                have (to_integer(at(region(3).entry, (i as int32))) + 1) <= 2147483647 by {
                    close() using { to_integer(at(region(3).entry, (i as int32))) <
                            to_integer(at(region(3).entry, length)); to_integer(at(region(3).entry, length)) <= 1073741823; };
                }
                have to_integer((i as int32)) == (to_integer(at(region(3).entry, (i as int32))) + 1) by {
                    close() using { -2147483648 <= (to_integer(at(region(3).entry, (i as int32))) + 1); (to_integer(at(region(3).entry, (i as int32))) + 1) <= 2147483647; };
                }
                close() using { to_integer((i as int32)) == (to_integer(at(region(3).entry, (i as int32))) + 1); };
            }
        }
    }
    have i == length;
    have forall (k: int32) { 0 <= k and k < length implies dst[k] == old(src[k]) } by {
        intro() {
            intro() {
                have at(loop(0).exit, 0) <= at(loop(0).exit, k) and at(loop(0).exit, k) < at(loop(0).exit, i);
                instantiate(forall (k: int32) { at(loop(0).exit, 0) <= at(loop(0).exit, k) and at(loop(0).exit, k) < at(loop(0).exit, i) implies at(loop(0).exit, dst[k]) == old(src[k]) }, k);
                close();
            }
        }
    }
    have forall (k: int32) { 0 <= k and k < length implies src[k] == old(src[k]) } by {
        intro() {
            intro() {
                instantiate(at(loop(0).exit, forall (k: int32) { 0 <= k and k < length implies src[k] == old(src[k]) }), k);
                close();
            }
        }
    }
    step();
    have forall (k: int32) { 0 <= k and k < length implies dst[k] == old(src[k]) } by {
        close();
    }
    close();
    close();
    close();
    close();
}

theorem vector_fields_separate_from_buffer(
    owner: Resource, length: Resource, capacity: Resource, data: Resource, buffer: Resource
) {
    requires separate(owner, buffer);
    requires contains(owner, length);
    requires contains(owner, capacity);
    requires contains(owner, data);
    ensures separate(buffer, (length * capacity) * data) by {
        apply(separation::contains_refl(buffer));
        apply(separation::separate_symm(owner, buffer));
        apply(separation::separate_restrict(buffer, owner, buffer, length));
        apply(separation::separate_restrict(buffer, owner, buffer, capacity));
        apply(separation::separate_restrict(buffer, owner, buffer, data));
        apply(separation::separate_star(length, capacity, buffer));
        apply(separation::separate_star(length * capacity, data, buffer));
        apply(separation::separate_symm((length * capacity) * data, buffer));
    }
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
        apply(integer::int32_less_equal_less_than_transitive(owner->cap, 536870910, 2147483647));
        close();
    }
    have (owner->cap + 1) <= 536870911 by {
        apply(integer::int32_less_equal_less_than_transitive(owner->cap, 536870910, 536870911));
        apply(integer::int32_increment_upper_bound(owner->cap, 536870911));
        close();
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
        close();
    }
    have owner->len <= owner->cap by {
        close();
    }
    have 1 <= new_capacity by {
        have 1 <= (owner->cap + 1) by {
            apply(integer::int32_increment_lower_bound(owner->cap, 1, 2147483647));
            close();
        }
        have 1 <= new_capacity by { close(); }
        close();
    }
    have owner->len <= old_capacity by {
        close();
    }
    have owner->len <= new_capacity by {
        have owner->len <= (owner->cap + 1) by {
            apply(integer::int32_increment_lower_bound(owner->cap, owner->len, 2147483647));
            close();
        }
        have owner->len <= new_capacity by { close(); }
        close();
    }
    have new_capacity <= 536870911 by {
        close();
    }
    have 0 <= new_capacity by {
        apply(integer::int32_less_equal_transitive(0, 1, new_capacity));
        close();
    }
    have 0 <= old_capacity by {
        have old_capacity == owner->cap by {
            close();
        }
        rewrite(old_capacity, owner->cap);
        apply(integer::int32_less_equal_transitive(0, 1, owner->cap));
        close();
    }
    have (new_capacity as uint32) <= 1073741823u32 by {
        close() using {
            0 <= new_capacity;
            new_capacity <= 536870911;
        };
    }
    have (old_capacity as uint32) <= 1073741823u32 by {
        have old_capacity == owner->cap by {
            close();
        }
        rewrite(old_capacity, owner->cap);
        have 0 <= to_integer(owner->cap) by close();
        have 536870910 <= 1073741823;
        apply(integer::int32_less_equal_transitive(owner->cap, 536870910, 1073741823));
        have to_integer(owner->cap) <= to_integer(1073741823u32) by {
            rewrite(to_integer(1073741823u32), to_integer(1073741823));
            apply(integer::int32_less_equal_to_integer(owner->cap, 1073741823));
        }
        apply(vector_nonnegative_as_uint32_bound(owner->cap, 1073741823u32));
    }
    have owner->len <= 536870910 by {
        apply(integer::int32_less_equal_transitive(owner->len, owner->cap, 536870910));
        close();
    }
    have (owner->len as uint32) <= 1073741823u32 by {
        have 0 <= to_integer(owner->len) by close();
        have 536870910 <= 1073741823;
        apply(integer::int32_less_equal_transitive(owner->len, 536870910, 1073741823));
        have to_integer(owner->len) <= to_integer(1073741823u32) by {
            rewrite(to_integer(1073741823u32), to_integer(1073741823));
            apply(integer::int32_less_equal_to_integer(owner->len, 1073741823));
        }
        apply(vector_nonnegative_as_uint32_bound(owner->len, 1073741823u32));
    }
    if new_data == 0 {
        step();
        step();
        have forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) } by {
            intro() {
                intro() {
                    have 0 <= k;
                    have k < old(owner->len);
                    have owner->data[k] == old(owner->data[k]) by { close(); }
                    close();
                }
            }
        }
        apply(vector_fields_separate_from_buffer(memory(*owner), memory(owner->len), memory(owner->cap), memory(owner->data), memory(owner->data[0..owner->cap])));
        let after = fold(allocated_vector(owner), { cap: owner->cap });
        have result == 0 by {
            close();
        }
        have result == 0 or result == 1 by {
            close();
        }
        have owner->len == old(owner->len) by {
            close();
        }
        have result == 0 implies owner->cap == old(owner->cap) by {
            close();
        }
        have result == 0 implies owner->data == old(owner->data) by {
            close();
        }
        have result == 1 implies owner->cap == (old(owner->cap) + 1) by {
            close();
        }
        close();
        close();
        close();
        close();
        close();
        close();
        close();
    } else {
        step();
        step();
        step();
        step_until(assignment(copied, 0).entry);
        step();
        have copied == owner->len by close();
        step_until(statement(14).entry);
        have 0 <= owner->len by {
            close();
        }
        have owner->cap == at(region(9).entry, new_capacity) by {
            close();
        }
        have owner->len <= owner->cap by {
            close();
        }
        have 1 <= owner->cap by {
            close();
        }
        have owner->cap <= 536870911 by {
            close();
        }
        have separate(memory(*owner), memory(owner->data[0..owner->cap])) by {
            close();
        }
        have owner->len == old(owner->len) by close();
        have forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) } by {
            intro() {
                intro() {
                    have at(statement(10).call(vector_copy, 0).entry, 0) <= at(statement(10).call(vector_copy, 0).entry, k) and at(statement(10).call(vector_copy, 0).entry, k) < at(statement(10).call(vector_copy, 0).entry, owner->len);
                    instantiate(forall (copy_index: int32) { at(statement(10).call(vector_copy, 0).entry, 0) <= at(statement(10).call(vector_copy, 0).entry, copy_index) and at(statement(10).call(vector_copy, 0).entry, copy_index) < at(statement(10).call(vector_copy, 0).entry, owner->len) implies at(statement(10).call(vector_copy, 0).exit, new_data[copy_index]) == at(statement(10).call(vector_copy, 0).entry, old_data[copy_index]) }, k);
                    have &owner->data[k] == at(region(14).entry, &new_data[k]) by {
                        close();
                    }
                    have separate(memory(owner->data[k]), memory(old(owner->data)[0..old(owner->cap)]));
                    have at(statement(10).call(vector_copy, 0).entry, old_data[k]) == old(owner->data[k]) by { close(); }
                    have k < new_capacity by { close(); }
                    have separate(memory(*owner), memory(new_data[0..new_capacity])) by { close(); }
                    have contains(memory(*owner), memory(owner->data)) by { close(); }
                    have contains(memory(*owner), memory(owner->cap)) by { close(); }
                    have separate(memory(owner->data), memory(new_data[k])) by {
                        apply(selected_array_cell(memory(*owner), memory(owner->data), new_data, new_capacity, k));
                    }
                    have separate(memory(owner->cap), memory(new_data[k])) by {
                        apply(selected_array_cell(memory(*owner), memory(owner->cap), new_data, new_capacity, k));
                    }
                    // Keep the copied cell across the two field writes and old-buffer release.
                    have separate(statement(11).footprint, memory(new_data[k])) by {
                        close() using { separate(memory(owner->data), memory(new_data[k])); };
                    }
                    have at(statement(11).exit, new_data[k]) == at(statement(11).entry, new_data[k]) by {
                        preserve(memory(new_data[k]), statement(11));
                    }
                    have separate(statement(12).footprint, memory(new_data[k])) by {
                        close() using { separate(memory(owner->cap), memory(new_data[k])); };
                    }
                    have at(statement(12).exit, new_data[k]) == at(statement(12).entry, new_data[k]) by {
                        preserve(memory(new_data[k]), statement(12));
                    }
                    have separate(statement(13).footprint, memory(new_data[k])) by {
                        close() using { separate(memory(owner->data[k]), memory(old(owner->data)[0..old(owner->cap)])); owner->data == new_data; };
                    }
                    have at(statement(13).exit, new_data[k]) == at(statement(13).entry, new_data[k]) by {
                        preserve(memory(new_data[k]), statement(13));
                    }
                    have owner->data == new_data by { close(); }
                    have new_data[k] == at(statement(10).call(vector_copy, 0).exit, new_data[k]) by { close(); }
                    have at(statement(10).call(vector_copy, 0).exit, new_data[k]) == at(statement(10).call(vector_copy, 0).entry, old_data[k]) by {
                        apply(at(statement(10).call(vector_copy, 0).entry, 0) <= at(statement(10).call(vector_copy, 0).entry, k) and at(statement(10).call(vector_copy, 0).entry, k) < at(statement(10).call(vector_copy, 0).entry, owner->len) implies at(statement(10).call(vector_copy, 0).exit, new_data[k]) == at(statement(10).call(vector_copy, 0).entry, old_data[k]));
                    }
                    have new_data[k] == old(owner->data[k]) by {
                        rewrite(new_data[k], at(statement(10).call(vector_copy, 0).exit, new_data[k]));
                        rewrite(old(owner->data[k]), at(statement(10).call(vector_copy, 0).entry, old_data[k]));
                        close();
                    }
                    rewrite(owner->data, new_data);
                    rewrite(new_data[k], old(owner->data[k]));
                    close();
                }
            }
        }
        step();
        apply(vector_fields_separate_from_buffer(memory(*owner), memory(owner->len), memory(owner->cap), memory(owner->data), memory(owner->data[0..owner->cap])));
        let after = fold(allocated_vector(owner), { cap: owner->cap });
        have result == 1 by {
            close();
        }
        have result == 0 or result == 1 by {
            close();
        }
        have owner->len == old(owner->len) by {
            close();
        }
        have result == 0 implies owner->cap == old(owner->cap) by {
            close();
        }
        have result == 0 implies owner->data == old(owner->data) by {
            close();
        }
        have result == 1 implies owner->cap == (old(owner->cap) + 1) by {
            close();
        }
        close();
        close();
        close();
        close();
        close();
        close();
        close();
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
        close();
    }
    have at(function.entry, owner->len) < at(function.entry, (owner->len + 1)) by {
        apply(integer::int32_increment_strictly_increases(at(function.entry, owner->len), at(function.entry, owner->cap)));
        close();
    }
    have result == (old(owner->len) + 1) by {
        close();
    }
    have owner->len == (old(owner->len) + 1) by {
        close();
    }
    have owner->data[old(owner->len)] == value by {
        close();
    }
    have owner->cap == old(owner->cap) by {
        close();
    }
    have owner->data == old(owner->data) by {
        close();
    }
    have forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) } by {
        intro() {
            intro() {
                have 0 <= k;
                have k < old(owner->len);
                have owner->data[k] == old(owner->data[k]) by { close(); }
                close();
            }
        }
    }
    close();
    close();
    close();
    close();
    close();
    close();
    close();
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
        let { after: after } = step(vector_grow, { before: ready });
        step_until(statement(2).statement(0).assignment(grown, 0).entry);
        step();
        if program::grown == 0 {
            unfold(after);
            apply(vector_fields_separate_from_buffer(memory(*owner), memory(owner->len), memory(owner->cap), memory(owner->data), memory(owner->data[0..owner->cap])));
            let after = fold(allocated_vector(owner), { cap: owner->cap });
            step();
            step();
            have not old(owner->len) < old(owner->cap) by {
                rewrite(at(function.entry, owner->len), at(function.entry, owner->cap));
                close();
            }
            have result == 0 by {
                close();
            }
            have result == 0 or result == 1 by {
                close();
            }
            have result == 0 implies owner->len == old(owner->len) by {
                intro() {
                    have owner->len == old(owner->len) by { close(); }
                    close();
                }
            }
            have result == 0 implies owner->cap == old(owner->cap) by {
                intro() {
                    have at(region(4).entry, owner->cap) == at(region(3).entry, owner->cap);
                    close();
                }
            }
            have result == 0 implies owner->data == old(owner->data) by {
                intro() {
                    have at(region(4).entry, owner->data) == at(region(3).entry, owner->data);
                    close();
                }
            }
            have result == 1 implies owner->len == (old(owner->len) + 1) by {
                intro() {
                    close();
                }
            }
            have result == 1 implies owner->data[old(owner->len)] == value by {
                intro() {
                    close();
                }
            }
            have forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) } by {
                close();
            }
            have old(owner->len) < old(owner->cap) implies result == 1 by {
                intro() {
                    close();
                }
            }
            have old(owner->len) < old(owner->cap) implies owner->cap == old(owner->cap) by {
                intro() {
                    close();
                }
            }
            have old(owner->len) < old(owner->cap) implies owner->data == old(owner->data) by {
                intro() {
                    close();
                }
            }
            have owner->cap == old(owner->cap) by {
                have at(region(4).entry, owner->cap) == at(region(3).entry, owner->cap);
                close();
            }
            have owner->cap <= old(owner->cap) by {
                rewrite(owner->cap, old(owner->cap));
                close();
            }
            have old(owner->cap) <= 536870910;
            have 536870910 < 2147483647 by close();
            have old(owner->cap) < 2147483647 by apply(integer::int32_less_equal_less_than_transitive(old(owner->cap), 536870910, 2147483647));
            have owner->cap <= old(owner->cap) + 1 by apply(integer::int32_increment_lower_bound(old(owner->cap), owner->cap, 2147483647));
            close();
            close();
            close();
            close();
            close();
            close();
            close();
            close();
            close();
            close();
            close();
            close();
        } else {
            step();
            step();
            unfold(after);
            have program::grown == 1 by {
                cases {
                    program::grown == 0 => {
                        close();
                    }
                    program::grown == 1 => {
                        close();
                    }
                }
            }
            have owner->len == old(owner->len) by {
                close();
            }
            have owner->cap == (old(owner->cap) + 1) by {
                have owner->cap == (old(owner->cap) + 1);
                close();
            }
            have at(function.entry, owner->cap) <= 536870911 by {
                close();
            }
            have 536870911 < 2147483647 by {
                close();
            }
            apply(integer::int32_less_equal_less_than_transitive(at(function.entry, owner->cap), 536870911, 2147483647));
            apply(integer::int32_increment_strictly_increases(at(function.entry, owner->cap), 2147483647));
            have owner->len < owner->cap by {
                rewrite(owner->len, old(owner->len));
                rewrite(owner->cap, (old(owner->cap) + 1));
                rewrite(at(function.entry, owner->len), at(function.entry, owner->cap));
                close();
            }
            fold(vector_storage(owner));
            step_until(statement(4).entry);
            have at(statement(3).exit, owner->data[at(statement(3).entry, owner->len)]) == at(statement(3).exit, value) by {
                close();
            }
            unfold(vector_storage(owner));
            have 0 <= owner->len by {
                close();
            }
            have owner->len <= owner->cap by {
                close();
            }
            have owner->cap == at(statement(3).entry, owner->cap) by {
                close();
            }
            have 1 <= at(statement(3).entry, owner->cap) by {
                close();
            }
            have at(statement(3).entry, owner->cap) <= 536870911 by {
                close();
            }
            have 1 <= owner->cap by {
                rewrite(owner->cap, at(statement(3).entry, owner->cap));
                close();
            }
            have owner->cap <= 536870911 by {
                rewrite(owner->cap, at(statement(3).entry, owner->cap));
                close();
            }
            apply(vector_fields_separate_from_buffer(memory(*owner), memory(owner->len), memory(owner->cap), memory(owner->data), memory(owner->data[0..owner->cap])));
            let after = fold(allocated_vector(owner), { cap: owner->cap });
            step();
            have not old(owner->len) < old(owner->cap) by {
                rewrite(at(function.entry, owner->len), at(function.entry, owner->cap));
                close();
            }
            have result == 0 or result == 1 by {
                have result == 1 by close();
                close();
            }
            have result == 0 implies owner->len == old(owner->len) by {
                close();
            }
            have result == 0 implies owner->cap == old(owner->cap) by {
                close();
            }
            have result == 0 implies owner->data == old(owner->data) by {
                close();
            }
            have at(statement(3).entry, owner->len) == old(owner->len) by {
                close();
            }
            have owner->len == (old(owner->len) + 1) by {
                rewrite(owner->len, (at(statement(3).entry, owner->len) + 1));
                rewrite(at(statement(3).entry, owner->len), old(owner->len));
                close();
            }
            have result == 1 implies owner->len == (old(owner->len) + 1) by {
                intro() {
                    close();
                }
            }
            have at(statement(3).entry, owner->len) < at(statement(3).entry, owner->cap) by {
                close();
            }
            have at(statement(3).entry, owner->len) == old(owner->len) by {
                close();
            }
            have owner->cap == at(statement(3).entry, owner->cap) by {
                close();
            }
            have old(owner->len) < owner->cap by close();
            have owner->data[old(owner->len)] == value by {
                rewrite(old(owner->len), at(statement(3).entry, owner->len));
                close();
            }
            have result == 1 implies owner->data[old(owner->len)] == value by {
                intro() {
                    close();
                }
            }
            have forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) } by {
                intro() {
                    intro() {
                        have 0 <= k;
                        have k < old(owner->len);
                        instantiate(forall (j: int32) { 0 <= j and j < old(owner->len) implies at(region(4).entry, owner->data[j]) == old(owner->data[j]) }, k);
                        have k < at(statement(3).entry, owner->len) by {
                            rewrite(at(statement(3).entry, owner->len), old(owner->len));
                            close();
                        }
                        instantiate(forall (j: int32) { 0 <= j and j < at(statement(3).entry, owner->len) implies at(statement(3).exit, owner->data[j]) == at(statement(3).entry, owner->data[j]) }, k);
                        have owner->data[k] == at(statement(3).entry, owner->data[k]) by {
                            close() using {
                                at(statement(3).exit, owner->data[k]) == at(statement(3).entry, owner->data[k]);
                                0 <= k;
                                k < at(statement(3).entry, owner->len);
                            };
                        }
                        have at(statement(3).entry, owner->data[k]) == old(owner->data[k]) by {
                            close() using {
                                at(region(4).entry, owner->data[k]) == old(owner->data[k]);
                                0 <= k;
                                k < old(owner->len);
                            };
                        }
                        rewrite(owner->data[k], at(statement(3).entry, owner->data[k]));
                        close();
                    }
                }
            }
            have old(owner->len) < old(owner->cap) implies result == 1 by {
                intro() {
                    close();
                }
            }
            have old(owner->len) < old(owner->cap) implies owner->cap == old(owner->cap) by {
                intro() {
                    close();
                }
            }
            have old(owner->len) < old(owner->cap) implies owner->data == old(owner->data) by {
                intro() {
                    close();
                }
            }
            have owner->cap == old(owner->cap) + 1 by {
                rewrite(owner->cap, at(statement(3).entry, owner->cap));
                close();
            }
            have owner->cap <= old(owner->cap) + 1 by {
                rewrite(owner->cap, old(owner->cap) + 1);
                close();
            }
            close();
            close();
            close();
            close();
            close();
            close();
            close();
            close();
            close();
            close();
            close();
            close();
        }
    } else {
        unfold(before);
        have owner->len <= owner->cap by {
            close();
        }
        have not owner->len == owner->cap by {
            close();
        }
        have owner->len < owner->cap by {
            apply(integer::int32_less_equal_and_not_equal_implies_less_than(owner->len, owner->cap));
            close();
        }
        have old(owner->len) < old(owner->cap) by {
            close();
        }
        step();
        step();
        step();
        step();
        fold(vector_storage(owner));
        step_until(statement(4).entry);
        unfold(vector_storage(owner));
        have 0 <= owner->len by {
            close();
        }
        have owner->len <= owner->cap by {
            close();
        }
        have 1 <= owner->cap by {
            rewrite(owner->cap, at(region(0).entry, owner->cap));
            close();
        }
        have owner->cap <= 536870911 by {
            rewrite(owner->cap, at(region(0).entry, owner->cap));
            close();
        }
        apply(vector_fields_separate_from_buffer(memory(*owner), memory(owner->len), memory(owner->cap), memory(owner->data), memory(owner->data[0..owner->cap])));
        let after = fold(allocated_vector(owner), { cap: owner->cap });
        step();
        have 0 == 0 by {
            close();
        }
        have at(region(0).entry, 0) <= at(region(0).entry, owner->len) by {
            close();
        }
        have at(region(0).entry, (owner->len + 1)) <= at(region(0).entry, owner->cap) by {
            have at(region(0).entry, owner->len) < at(region(0).entry, owner->cap) by close();
            apply(integer::int32_increment_upper_bound(at(region(0).entry, owner->len), at(region(0).entry, owner->cap)));
            close();
        }
        have result == 1 by {
            close();
        }
        have result == 0 or result == 1 by {
            close();
        }
        have result == 0 implies owner->len == old(owner->len) by {
            close();
        }
        have result == 0 implies owner->cap == old(owner->cap) by {
            close();
        }
        have result == 0 implies owner->data == old(owner->data) by {
            close();
        }
        have result == 1 implies owner->len == (old(owner->len) + 1) by {
            intro() {
                close();
            }
        }
        have owner->data[old(owner->len)] == value by {
            close();
        }
        have result == 1 implies owner->data[old(owner->len)] == value by {
            intro() {
                close();
            }
        }
        have forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) } by {
            close();
        }
        have owner->cap == old(owner->cap) by {
            close();
        }
        have owner->data == old(owner->data) by {
            close();
        }
        have old(owner->len) < old(owner->cap) implies result == 1 by {
            intro() {
                close();
            }
        }
        have old(owner->len) < old(owner->cap) implies owner->cap == old(owner->cap) by {
            intro() {
                close();
            }
        }
        have old(owner->len) < old(owner->cap) implies owner->data == old(owner->data) by {
            intro() {
                close();
            }
        }
        have owner->cap <= old(owner->cap) by {
            rewrite(owner->cap, old(owner->cap));
            close();
        }
        have old(owner->cap) <= 536870910;
        have 536870910 < 2147483647 by close();
        have old(owner->cap) < 2147483647 by apply(integer::int32_less_equal_less_than_transitive(old(owner->cap), 536870910, 2147483647));
        have owner->cap <= old(owner->cap) + 1 by apply(integer::int32_increment_lower_bound(old(owner->cap), owner->cap, 2147483647));
        close();
        close();
        close();
        close();
        close();
        close();
        close();
        close();
        close();
        close();
        close();
        close();
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
        &(argument as (struct shared_log *))->mu,
        log_state(argument as (struct shared_log *))
    );
    consumes credit(argument as (struct shared_log *));
    ensures result == 0;
} by {
    step();
    step();
    let { guard: guard, state: state } = step(pthread_mutex_lock, { access: access }
    );
    let { cap: cap, slack: slack, items: items } = unfold(state);
    have count(credit(log)) >= 1;
    have slack == count(credit(log));
    have 1 <= slack;
    unfold(credit(log));
    have to_integer(1) <= to_integer(slack) by apply(integer::int32_less_equal_to_integer(1, slack));
    have to_integer(cap) <= to_integer(536870909) by close() using {
        to_integer(cap) + to_integer(slack) <= 536870910;
        to_integer(1) <= to_integer(slack);
        to_integer(1) == 1;
        to_integer(536870909) == 536870909;
    };
    have cap <= 536870909 by apply(integer::int32_to_integer_less_equal_implies_less_equal(cap, 536870909));
    have items.cap == cap;
    let { cap: items_cap } = unfold(items);
    have log->items->cap == items_cap;
    have log->items->cap == cap;
    have log->items->cap <= 536870910;
    let ready = fold(allocated_vector(log->items), { cap: log->items->cap });
    let { after: after } = step(allocated_vector_push, { before: ready });
    let { cap: pushed_cap } = unfold(after);
    have log->items->cap <= at(region(3).entry, log->items->cap) + 1;
    have at(region(3).entry, log->items->cap) == cap;
    have log->items->cap == pushed_cap;
    have pushed_cap == log->items->cap;
    have cap == at(region(3).entry, log->items->cap);
    have pushed_cap <= cap + 1 by {
        rewrite(pushed_cap, log->items->cap);
        rewrite(cap, at(region(3).entry, log->items->cap));
        close();
    }
    have defined(cap + 1);
    have defined(slack - 1);
    have to_integer(cap + 1) == to_integer(cap) + to_integer(1) by apply(integer::int32_add_to_integer(cap, 1));
    have to_integer(slack - 1) == to_integer(slack) - to_integer(1) by apply(integer::int32_subtract_to_integer(slack, 1));
    have to_integer(pushed_cap) <= to_integer(cap + 1) by apply(integer::int32_less_equal_to_integer(pushed_cap, cap + 1));
    have to_integer(pushed_cap) + to_integer(slack - 1) <= 536870910 by close() using {
        to_integer(pushed_cap) <= to_integer(cap + 1);
        to_integer(cap + 1) == to_integer(cap) + to_integer(1);
        to_integer(slack - 1) == to_integer(slack) - to_integer(1);
        to_integer(cap) + to_integer(slack) <= 536870910;
    };
    let pushed = fold(allocated_vector(log->items), { cap: log->items->cap });
    let restored = fold(log_state(log), { cap: pushed_cap, slack: slack - 1, items: pushed });
    step(pthread_mutex_unlock, {
        access: access, guard: guard, state: restored
    });
    step();
    close();
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
    have to_integer(before.cap) <= to_integer(536870908) by apply(integer::int32_less_equal_to_integer(before.cap, 536870908));
    have to_integer(before.cap) + to_integer(2) <= 536870910 by close() using {
        to_integer(before.cap) <= to_integer(536870908);
        to_integer(536870908) == 536870908;
        to_integer(2) == 2;
    };
    let state = fold(log_state(log), { cap: before.cap, slack: 2, items: before });
    let { lifetime: lifetime } = step(pthread_mutex_init, { state: state });
    branch {
        true => {
            let { cap: cap1, slack: slack1, items: after } = unfold(state);
            unfold(credit(log));
            unfold(credit(log));
            step();
            close();
        }
        false => {}
    }
    step();
    branch {
        true => {
            step(pthread_mutex_destroy, { lifetime: lifetime });
            let { cap: cap2, slack: slack2, items: after } = unfold(state);
            unfold(credit(log));
            unfold(credit(log));
            step();
            close();
        }
        false => {}
    }
    step();
    branch {
        true => {
            step();
            step(pthread_mutex_destroy, { lifetime: lifetime });
            let { cap: cap3, slack: slack3, items: after } = unfold(state);
            unfold(credit(log));
            step();
            close();
        }
        false => {}
    }
    step();
    step();
    step(pthread_mutex_destroy, { lifetime: lifetime });
    let { cap: cap4, slack: slack4, items: after } = unfold(state);
    step();
    close();
}
