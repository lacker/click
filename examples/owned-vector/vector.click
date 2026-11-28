import click::separation;

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
    owns *owner;
    owns owner->data[0..owner->cap];
    fact owner->len == 0;
    fact 1 <= owner->cap;
    fact owner->cap <= 1073741823;
    fact separate(memory(*owner), memory(owner->data[0..owner->cap]));
}

resource nonempty_vector(owner: struct vector*) {
    owns *owner;
    owns owner->data[0..owner->cap];
    fact 1 <= owner->len;
    fact owner->len <= owner->cap;
    fact owner->cap <= 1073741823;
    fact separate(memory(*owner), memory(owner->data[0..owner->cap]));
}

resource vector_storage(owner: struct vector*) {
    owns *owner;
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
    fact owner->cap <= 1073741823;
    fact separate(memory(*owner), memory(owner->data[0..owner->cap]));
}

resource allocated_vector(owner: struct vector*) {
    owns *owner;
    owns allocation(owner->data, owner->cap * 4);
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
    fact 1 <= owner->cap;
    fact owner->cap <= 536870911;
    fact separate(memory(*owner), memory(owner->data[0..owner->cap]));
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

int32 vector_grow(struct vector* owner) {
    let entry_length = old(owner->len);
    let entry_capacity = old(owner->cap);

    requires owner->cap <= 536870910;
    owns allocated_vector(owner);
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
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    have 0 <= old_capacity by {
        rewrite(old_capacity, owner->cap);
        have 0 <= owner->cap;
        close();
    }
    have (old_capacity as uint32) <= 1073741823u32 by {
        rewrite(old_capacity, owner->cap);
        have 0 <= to_integer(owner->cap);
        have to_integer(owner->cap) <= to_integer(1073741823u32);
        apply(vector_nonnegative_as_uint32_bound(owner->cap, 1073741823u32));
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
        fold(allocated_vector(owner));
        have result == 0;
        have result == 0 implies owner->cap == old(owner->cap);
        have result == 0 implies owner->data == old(owner->data);
        have result == 1 implies owner->cap == (old(owner->cap) + 1);
        close();
        close();
        close();
        close();
        close();
        close();
        close();
    } else {
        have 1 <= new_capacity by { close() using { 1 <= old_capacity; old_capacity <= 536870911; }; }
        have new_capacity <= 536870912 by { close() using { 1 <= old_capacity; old_capacity <= 536870911; }; }
        have (new_capacity as uint32) <= 1073741823u32 by {
            close() using { 1 <= new_capacity; new_capacity <= 536870912; };
        }
        have (owner->len as uint32) <= 1073741823u32 by {
            have 0 <= to_integer(owner->len);
            have to_integer(owner->len) <= to_integer(1073741823u32);
            apply(vector_nonnegative_as_uint32_bound(owner->len, 1073741823u32));
        }
        step();
        step();
        step();
        step();
        step();
        step();
        step();
        have owner->cap == at(region(9).entry, new_capacity);
        have owner->data == at(region(14).entry, new_data);
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
        fold(allocated_vector(owner));
        have result == 0 implies owner->cap == old(owner->cap);
        have result == 0 implies owner->data == old(owner->data);
        have owner->cap == old(owner->cap) + 1 by {
            rewrite(owner->cap, at(region(9).entry, new_capacity));
            have at(region(9).entry, new_capacity) == at(region(5).exit, old_capacity) + 1;
            rewrite(at(region(9).entry, new_capacity), at(region(5).exit, old_capacity) + 1);
            have at(region(5).exit, old_capacity) == old(owner->cap);
            rewrite(at(region(5).exit, old_capacity), old(owner->cap));
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
    have forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) } by {
        intro() {
            intro() {
                have 0 <= k;
                have k < old(owner->len);
                // The append writes at the old length, beyond this prefix element.
                have old(owner->len) != k by {
                    if old(owner->len) == k {
                        have not (k < old(owner->len)) by {
                            rewrite(old(owner->len), k);
                            close();
                        }
                        close();
                    } else {
                        close();
                    }
                }
                have separate(memory(old(owner->data)[old(owner->len)]), memory(old(owner->data)[k])) by {
                    apply(click::separation::separate_elements(old(owner->data), old(owner->len), k));
                }
                have separate(statement(4).footprint, memory(old(owner->data)[k])) by {
                    close() using { separate(memory(old(owner->data)[old(owner->len)]), memory(old(owner->data)[k])); };
                }
                have at(statement(4).exit, owner->data[k]) == at(statement(4).entry, owner->data[k]) by {
                    preserve(memory(old(owner->data)[k]), statement(4));
                }
                // Restrict the struct/array separation to the length field and element.
                have k < old(owner->cap) by {
                    apply(click::integer::int32_less_than_less_equal_transitive(k, old(owner->len), old(owner->cap)));
                }
                have contains(memory(*owner), memory(owner->len)) by { close(); }
                have contains(memory(old(owner->data)[0..old(owner->cap)]), memory(old(owner->data)[k])) by {
                    apply(click::separation::contains_element(old(owner->data), 0, old(owner->cap), k));
                }
                have separate(memory(owner->len), memory(old(owner->data)[k])) by {
                    apply(click::separation::separate_restrict(memory(*owner), memory(old(owner->data)[0..old(owner->cap)]), memory(owner->len), memory(old(owner->data)[k])));
                }
                have separate(statement(5).footprint, memory(old(owner->data)[k])) by {
                    close() using { separate(memory(owner->len), memory(old(owner->data)[k])); };
                }
                have at(statement(5).exit, owner->data[k]) == at(statement(5).entry, owner->data[k]) by {
                    preserve(memory(old(owner->data)[k]), statement(5));
                }
                close();
            }
        }
    }
    step();
    have owner->data == old(owner->data) by {
        close();
    }
    have owner->data[old(owner->len)] == value by {
        close();
    }
    fold(vector_storage(owner));
    close();
}

int32 allocated_vector_push(struct vector* owner, int32 value) {
    requires owner->cap <= 536870910;
    owns allocated_vector(owner);
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
        with(allocated_vector(owner)) {
            step();
            have separate(statement(0).footprint, memory(owner->data)) by { close() using {}; }
            have owner->data == at(statement(0).entry, owner->data) by {
                preserve(memory(owner->data), statement(0));
            }
            step();
            have separate(statement(1).footprint, memory(owner->data)) by { close() using {}; }
            have owner->data == at(statement(1).entry, owner->data) by {
                preserve(memory(owner->data), statement(1));
            }
            step();
        }
        mark before_grow;
        step();
        mark after_grow;
        step();
        have separate(memory(grown), memory(owner->data)) by { close(); }
        have separate(statement(2).statement(0).assignment(grown, 0).footprint, memory(owner->data)) by {
            close() using { separate(memory(grown), memory(owner->data)); };
        }
        have owner->data == at(after_grow, owner->data) by {
            preserve(memory(owner->data), statement(2).statement(0).assignment(grown, 0));
        }
        have program::grown == 0 implies owner->data == at(before_grow, owner->data) by {
            intro() {
                have at(after_grow, owner->data) == at(before_grow, owner->data);
                close();
            }
        }
        if program::grown == 0 {
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
                    have at(region(5).entry, owner->cap) == at(region(3).entry, owner->cap);
                    close();
                }
            }
            have result == 0 implies owner->data == old(owner->data) by {
                intro() {
                    have at(region(5).entry, owner->data) == at(region(3).entry, owner->data);
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
            unfold(allocated_vector(owner));
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
            have owner->cap == (old(owner->cap) + 1) by close();
            have owner->len < owner->cap;
            fold(vector_storage(owner));
            step();
            step();
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
            fold(allocated_vector(owner));
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
            have old(owner->len) < owner->cap by {

                close();
            }
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
                        instantiate(forall (j: int32) { 0 <= j and j < old(owner->len) implies at(region(5).entry, owner->data[j]) == old(owner->data[j]) }, k);
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
                                at(region(5).entry, owner->data[k]) == old(owner->data[k]);
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
        observe(allocated_vector(owner));
        have owner->len <= owner->cap by {
            close();
        }
        have not owner->len == owner->cap by {
            close();
        }
        have owner->len < owner->cap by close();
        have old(owner->len) < old(owner->cap) by {
            close();
        }
        step();
        step();
        step();
        step();
        unfold(allocated_vector(owner));
        fold(vector_storage(owner));
        step();
        step();
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
        fold(allocated_vector(owner));
        step();
        have 0 == 0 by {
            close();
        }
        have at(region(0).entry, 0) <= at(region(0).entry, owner->len) by {
            close();
        }
        have at(region(0).entry, (owner->len + 1)) <= at(region(0).entry, owner->cap);
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

int32 vector_init(struct vector* owner, int32 data[], int32 capacity) {
    requires 1 <= capacity;
    requires capacity <= 1073741823;
    consumes *owner;
    consumes data[0..capacity];
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
    have result == 0;
    close();
    close();
    close();
    close();
    close();
}

int32 vector_len(struct vector* owner) {
    views nonempty_vector(owner);

    ensures result == owner->len by {
        step();
        close();
    }
}

int32 vector_get(struct vector* owner, int32 index) {
    requires 0 <= index;
    requires index < owner->len;
    views nonempty_vector(owner);

    ensures result == owner->data[index];
    ensures result == old(owner->data[index]);
} by {
    step();
    step();
    step();
    close();
    close();
}

int32 vector_set(struct vector* owner, int32 index, int32 value) {
    requires 0 <= index;
    requires index < owner->len;
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
    close();
    close();
    close();
    close();
    close();
    close();
}

int32 vector_fill(struct vector* owner, int32 value) {
    owns nonempty_vector(owner);
    ensures result == owner->len;
} by {
    unfold(nonempty_vector(owner));
    step();
    step();
    have i >= 0;
    have i <= owner->len;
    loop fill_cells {
        decreases owner->len - i;
        invariant i >= 0 and i <= owner->len;
        invariant owner->len == old(owner->len);
        invariant owner->data == old(owner->data);
        owns owner->data[0..owner->len];
        initialize by close();
        maintain by {
            mark before_fill;
            have i < owner->cap;
            have contains(memory(*owner), memory(owner->data)) by { close(); }
            have separate(memory(owner->data), memory(owner->data[i])) by {
                apply(selected_array_cell(memory(*owner), memory(owner->data),
                    owner->data, owner->cap, i));
            }
            have contains(memory(*owner), memory(owner->len)) by { close(); }
            have separate(memory(owner->len), memory(owner->data[i])) by {
                apply(selected_array_cell(memory(*owner), memory(owner->len), owner->data, owner->cap, i));
            }
            step();
            have separate(loop(0).statement(0).footprint, memory(owner->data)) by {
                close() using {
                    at(before_fill, separate(memory(owner->data), memory(owner->data[i])));
                };
            }
            have owner->data == at(before_fill, owner->data) by {
                preserve(memory(owner->data), loop(0).statement(0));
            }
            have owner->data == old(owner->data) by {
                close() using {
                    owner->data == at(before_fill, owner->data);
                    at(before_fill, owner->data) == old(owner->data);
                };
            }
            have separate(loop(0).statement(0).footprint, memory(owner->len)) by {
                close() using { at(before_fill, separate(memory(owner->len), memory(owner->data[i]))); };
            }
            have owner->len == at(before_fill, owner->len) by {
                preserve(memory(owner->len), loop(0).statement(0));
            }
            have owner->len == old(owner->len) by { close(); }
            step();
            have 0 - at(region(3).entry, i) + owner->len - 1
                < 0 - at(region(3).entry, i) + owner->len;
        }
    }
    step();
    fold(nonempty_vector(owner));
    close();
    close();
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

    ensures replace != 0 implies result == replacement;
} by {
    step();
    step();
    step();
    step();
    branch {
        true => {
            step();
            step();
            have replace != 0 implies selected == replacement;
        }
        false => {
            step();
            step();
            have replace != 0 implies selected == replacement by {
                intro() {
                    close();
                }
            }
        }
    }
    step();
    close();
    close();
}

int32 vector_clear(struct vector* owner) {
    consumes nonempty_vector(owner);
    produces empty_vector(owner);
    ensures result == 0;
    ensures owner->len == 0;
} by {
    unfold(nonempty_vector(owner));
    step();
    step();
    have owner->len == 0;
    have 1 <= at(region(0).entry, owner->cap);
    have 1 <= owner->cap by { close(); }
    close();
    fold(empty_vector(owner));
    close();
    close();
}

int32 vector_pipeline(
    struct vector* owner,
    int32 data[],
    int32 capacity,
    int32 first,
    int32 replacement
) {
    requires 1 <= capacity;
    requires capacity <= 1073741823;
    consumes *owner;
    consumes data[0..capacity];

    produces empty_vector(owner);
    ensures result == replacement;
} by {
    step();
    step();
    step();
    step();
    unfold(empty_vector(owner));
    fold(vector_storage(owner));
    step();
    step();
    unfold(vector_storage(owner));
    fold(nonempty_vector(owner));
    step();
    step();
    step();
    step();
    observe(nonempty_vector(owner));
    step();
    step();
    apply(int32_equality_transitive(observed, owner->data[0], replacement));
    step();
    step();
    step();
    close();
    close();
}
