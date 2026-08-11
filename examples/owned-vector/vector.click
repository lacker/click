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
        invariant forall (k: int32) {
            0 <= k and k < i implies dst[k] == old(src[k])
        };
        mutable dst[0..length] by frame;
    }
    have i == length by simp;
    have forall (k: int32) {
        0 <= k and k < length implies dst[k] == old(src[k])
    } by simp;
    step();
    frame();
    have result == length by {
        assumption();
    }
    have forall (k: int32) { 0 <= k and k < length implies src[k] == old(src[k]) } by {
        derive using {
            0 <= length;
            length <= dst_capacity;
            length <= src_capacity;
            1 <= dst_capacity;
            1 <= src_capacity;
            at(statement(0).entry, loadable(dst[0..dst_capacity]));
            at(statement(0).entry, loadable(src[0..src_capacity]));
            separate(memory(dst[0..dst_capacity]), memory(src[0..src_capacity]));
            at(loop(0).exit, 0) <= at(loop(0).exit, i);
            at(loop(0).exit, i) <= at(loop(0).exit, length);
            not at(loop(0).exit, i) < at(loop(0).exit, length);
            at(statement(5).entry, i) == at(statement(5).entry, length);
            forall (k: int32) { at(loop(0).exit, 0) <= at(loop(0).exit, k) and at(loop(0).exit, k) < at(loop(0).exit, i) implies at(loop(0).exit, dst[k]) == old(src[k]) };
            forall (k: int32) { 0 <= k and k < length implies dst[k] == old(src[k]) };
        }
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
    have owner->cap < 2147483647 by simp;
    have owner->cap + 1 <= 536870911 by simp;
    execute_until(statement(9));
    have 0 <= owner->len by simp;
    have owner->len <= owner->cap by simp;
    have 1 <= new_capacity by simp;
    have owner->len <= old_capacity by simp;
    have owner->len <= new_capacity by simp;
    have new_capacity <= 536870911 by simp;
    have loadable(old_data[0..old_capacity]) by {
        simp() using {
            loadable(old(owner->data[0..owner->cap]));
        }
    }
    if new_data == 0 {
        have loadable(owner->data[0..owner->cap]) by {
            simp() using {
                loadable(old(owner->data[0..owner->cap]));
            }
        }
        execute();
        have forall (k: int32) {
            0 <= k and k < old(owner->len) implies
                owner->data[k] == old(owner->data[k])
        } by simp;
        fold(allocated_vector(owner));
        frame();
        have result == 0 by simp;
        have result == 0 or result == 1 by simp;
        have owner->len == old(owner->len) by simp;
        have result == 0 implies owner->cap == old(owner->cap) by simp;
        have result == 0 implies owner->data == old(owner->data) by simp;
        have result == 1 implies owner->cap == old(owner->cap) + 1 by simp;
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
        step() using {}
        step();
        have 0 <= owner->len by {
            assumption();
        }
        have owner->cap == at(statement(9).entry, new_capacity) by {
            normalize();
        }
        have owner->len <= owner->cap by {
            simp() using {
                at(statement(9).entry, owner->len <= new_capacity);
                owner->cap == at(statement(9).entry, new_capacity);
            }
        }
        have 1 <= owner->cap by {
            simp() using {
                at(statement(9).entry, 1 <= new_capacity);
                owner->cap == at(statement(9).entry, new_capacity);
            }
        }
        have owner->cap <= 536870911 by {
            simp() using {
                at(statement(9).entry, new_capacity <= 536870911);
                owner->cap == at(statement(9).entry, new_capacity);
            }
        }
        have separate(
            memory(object(owner)),
            memory(owner->data[0..owner->cap])
        ) by simp;
        have forall (k: int32) {
            0 <= k and k < old(owner->len) implies
                owner->data[k] == old(owner->data[k])
        } by simp;
        have loadable(owner->data[0..owner->len]) by {
            transport(
                forall (k: int32) {
                    0 <= k and k < old(owner->len) implies
                        owner->data[k] == old(owner->data[k])
                },
                loadable(owner->data[0..owner->len])
            ) using {
                forall (k: int32) {
                    0 <= k and k < old(owner->len) implies
                        owner->data[k] == old(owner->data[k])
                };
            }
            assumption();
        }
        fold(allocated_vector(owner));
        frame();
        have result == 1 by simp;
        have result == 0 or result == 1 by simp;
        have owner->len == old(owner->len) by simp;
        have result == 0 implies owner->cap == old(owner->cap) by simp;
        have result == 0 implies owner->data == old(owner->data) by simp;
        have result == 1 implies owner->cap == old(owner->cap) + 1 by simp;
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
    execute();
    fold(vector_storage(owner));
    frame();
    simp();
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
    observe(allocated_vector(owner));
    if owner->len == owner->cap {
        step();
        step();
        step();
        step();
        if c(grown) == 0 {
            step();
            execute();
            have not (old(owner->len) < old(owner->cap)) by {
                simp() using {
                    at(function.entry, owner->len == owner->cap);
                }
            }
            frame();
            have result == 0 by simp;
            have result == 0 or result == 1 by simp;
            have result == 0 implies owner->len == old(owner->len) by simp;
            have result == 0 implies owner->cap == old(owner->cap) by simp;
            have result == 0 implies owner->data == old(owner->data) by simp;
            have result == 1 implies owner->len == old(owner->len) + 1 by simp;
            have result == 1 implies owner->data[old(owner->len)] == value by simp;
            have forall (k: int32) {
                0 <= k and k < old(owner->len) implies
                    owner->data[k] == old(owner->data[k])
            } by simp;
            have old(owner->len) < old(owner->cap) implies result == 1 by {
                intro();
                transport(
                    not (old(owner->len) < old(owner->cap)),
                    not (old(owner->len) < old(owner->cap))
                ) using {
                    not (old(owner->len) < old(owner->cap));
                }
                contradiction(old(owner->len) < old(owner->cap));
            }
            have old(owner->len) < old(owner->cap) implies
                owner->cap == old(owner->cap) by {
                intro();
                transport(
                    not (old(owner->len) < old(owner->cap)),
                    not (old(owner->len) < old(owner->cap))
                ) using {
                    not (old(owner->len) < old(owner->cap));
                }
                contradiction(old(owner->len) < old(owner->cap));
            }
            have old(owner->len) < old(owner->cap) implies
                owner->data == old(owner->data) by {
                derive using {
                    not (old(owner->len) < old(owner->cap));
                }
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
            have c(grown) == 1 by simp;
            have owner->len == old(owner->len) by simp;
            have owner->cap == old(owner->cap) + 1 by simp;
            have owner->len < owner->cap by {
                derive using {
                    at(function.entry, owner->len == owner->cap);
                    owner->len == old(owner->len);
                    owner->cap == old(owner->cap) + 1;
                }
            }
            fold(vector_storage(owner));
            step() using {
                owner->len < owner->cap;
                loadable(owner->len);
                loadable(owner->cap);
                loadable(owner->data);
            }
            unfold(vector_storage(owner));
            have 0 <= owner->len by simp;
            have owner->len <= owner->cap by simp;
            have 1 <= owner->cap by simp;
            have owner->cap <= 536870911 by simp;
            fold(allocated_vector(owner));
            step() using {}
            simp();
        }
    } else {
        observe(allocated_vector(owner));
        have owner->len <= owner->cap by {
            assumption();
        }
        have not (owner->len == owner->cap) by {
            assumption();
        }
        have owner->len < owner->cap by simp;
        have old(owner->len) < old(owner->cap) by simp;
        execute_until(statement(8));
        unfold(allocated_vector(owner));
        fold(vector_storage(owner));
        step() using {
            owner->len < owner->cap;
            loadable(owner->len);
            loadable(owner->cap);
            loadable(owner->data);
        }
        unfold(vector_storage(owner));
        have 0 <= owner->len by simp;
        have owner->len <= owner->cap by simp;
        have 1 <= owner->cap by simp;
        have owner->cap <= 536870911 by simp;
        fold(allocated_vector(owner));
        step() using {}
        have 0 == 0 by {
            normalize();
        }
        have at(statement(0).entry, 0) <=
            at(statement(0).entry, owner->len) by {
            assumption();
        }
        have at(statement(0).entry, (owner->len + 1)) <=
            at(statement(0).entry, owner->cap) by {
            have at(statement(0).entry, owner->len) <
                at(statement(0).entry, owner->cap) by {
                transport(
                    owner->len < owner->cap,
                    at(statement(0).entry, owner->len) <
                        at(statement(0).entry, owner->cap)
                ) using {
                    owner->len < owner->cap;
                }
                assumption();
            }
            apply(int32_increment_upper_bound(
                at(statement(0).entry, owner->len),
                at(statement(0).entry, owner->cap)
            )) using {
                at(statement(0).entry, owner->len) <
                    at(statement(0).entry, owner->cap);
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
        have result == 1 by simp;
        have result == 0 or result == 1 by simp;
        have result == 0 implies owner->len == old(owner->len) by simp;
        have result == 0 implies owner->cap == old(owner->cap) by simp;
        have result == 0 implies owner->data == old(owner->data) by simp;
        have result == 1 implies owner->len == old(owner->len) + 1 by simp;
        have owner->data[old(owner->len)] == value by {
            assumption();
        }
        have result == 1 implies owner->data[old(owner->len)] == value by {
            intro();
            assumption();
        }
        have forall (k: int32) {
            0 <= k and k < old(owner->len) implies
                owner->data[k] == old(owner->data[k])
        } by {
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
        have old(owner->len) < old(owner->cap) implies
            owner->cap == old(owner->cap) by {
            intro();
            assumption();
        }
        have old(owner->len) < old(owner->cap) implies
            owner->data == old(owner->data) by {
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
    execute();
    fold(empty_vector(owner));
    frame();
    simp();
}

int32 vector_len(struct vector* owner) {
    views nonempty_vector(owner);
    immutable;

    ensures result == owner->len by auto;
}

int32 vector_get(struct vector* owner, int32 index) {
    requires 0 <= index;
    requires index < owner->len;
    views nonempty_vector(owner);
    immutable;

    ensures result == owner->data[index];
    ensures result == old(owner->data[index]);
} by {
    execute();
    frame();
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
    step() using {
        0 <= index;
        index < owner->len;
        loadable(old(owner->len));
        loadable(old(owner->cap));
        loadable(old(owner->data));
        1 <= owner->len;
        owner->len <= owner->cap;
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
    }
    fold(nonempty_vector(owner));
    have index < index + 1 by simp;
    frame();
    simp();
}

int32 vector_fill(struct vector* owner, int32 value) {
    owns nonempty_vector(owner);
    mutable owner->data[0..owner->len];
    ensures result == owner->len;
} by {
    unfold(nonempty_vector(owner));
    step() using {
        separate(memory(owner->len), memory(owner->cap));
        separate(memory(owner->len), memory(owner->data));
        separate(memory(owner->len), memory(owner->data[0..owner->cap]));
        separate(memory(owner->cap), memory(owner->data));
        separate(memory(owner->cap), memory(owner->data[0..owner->cap]));
        separate(memory(owner->data), memory(owner->data[0..owner->cap]));
        contains(nonempty_vector(owner), memory(owner->len));
        contains(nonempty_vector(owner), memory(owner->cap));
        contains(nonempty_vector(owner), memory(owner->data));
        contains(nonempty_vector(owner), memory(owner->data[0..owner->cap]));
        loadable(owner->len);
        loadable(owner->cap);
        loadable(owner->data);
        loadable(owner->data[0..owner->cap]);
        1 <= owner->len;
        owner->len <= owner->cap;
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
    }
    step() using {
        separate(memory(owner->len), memory(owner->cap));
        separate(memory(owner->len), memory(owner->data));
        separate(memory(owner->len), memory(owner->data[0..owner->cap]));
        separate(memory(owner->cap), memory(owner->data));
        separate(memory(owner->cap), memory(owner->data[0..owner->cap]));
        separate(memory(owner->data), memory(owner->data[0..owner->cap]));
        contains(nonempty_vector(owner), memory(owner->len));
        contains(nonempty_vector(owner), memory(owner->cap));
        contains(nonempty_vector(owner), memory(owner->data));
        contains(nonempty_vector(owner), memory(owner->data[0..owner->cap]));
        loadable(old(owner->len));
        loadable(old(owner->cap));
        loadable(old(owner->data));
        loadable(old(owner->data[0..owner->cap]));
        1 <= owner->len;
        owner->len <= owner->cap;
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
    }
    have loadable(owner->len) by {
        simp() using {
            loadable(old(owner->len));
        }
    }
    have loadable(owner->cap) by {
        simp() using {
            loadable(old(owner->cap));
        }
    }
    have loadable(owner->data) by {
        simp() using {
            loadable(old(owner->data));
        }
    }
    have loadable(owner->data[0..owner->cap]) by {
        simp() using {
            loadable(old(owner->data[0..owner->cap]));
        }
    }
    have i >= 0 by {
        normalize();
    }
    have i <= owner->len by {
        simp() using {
            1 <= owner->len;
        }
    }
    loop as fill_cells {
        invariant i >= 0 and i <= owner->len;
        mutable owner->data[0..owner->len] by frame;
        initialize by simp;
        preserve by {
            have i < owner->cap by simp;
            step();
            step();
            have i >= 0 by {
                simp() using {
                    at(statement(3).entry, i) >= 0;
                    at(statement(3).entry, i) < at(statement(3).entry, owner->len);
                }
            }
            have i <= owner->len by {
                simp() using {
                    at(statement(3).entry, i) < at(statement(3).entry, owner->len);
                }
            }
            close_invariants();
        }
    }
    step() using {
        separate(memory(owner->len), memory(owner->cap));
        separate(memory(owner->len), memory(owner->data));
        separate(memory(owner->len), memory(owner->data[0..owner->cap]));
        separate(memory(owner->cap), memory(owner->data));
        separate(memory(owner->cap), memory(owner->data[0..owner->cap]));
        separate(memory(owner->data), memory(owner->data[0..owner->cap]));
        contains(nonempty_vector(owner), memory(owner->len));
        contains(nonempty_vector(owner), memory(owner->cap));
        contains(nonempty_vector(owner), memory(owner->data));
        contains(nonempty_vector(owner), memory(owner->data[0..owner->cap]));
        loadable(old(owner->len));
        loadable(old(owner->cap));
        loadable(old(owner->data));
        loadable(old(owner->data[0..owner->cap]));
        1 <= owner->len;
        owner->len <= owner->cap;
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        i >= 0;
        at(statement(0).entry, i) <= at(statement(0).entry, owner->len);
        not i < owner->len;
    }
    frame();
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
    step() using {
        index < owner->len;
        0 <= index;
        1 <= owner->len;
        owner->len <= owner->cap;
        loadable(old(owner->cap));
        loadable(old(owner->data));
        loadable(old(owner->len));
    }
    have replace == replace by {
        normalize();
    }
    branch {
        then {
            step() using {
                index < owner->len;
                0 <= index;
                1 <= owner->len;
                owner->len <= owner->cap;
                replace != 0;
                loadable(old(owner->cap));
                loadable(old(owner->data));
                loadable(old(owner->len));
            }
            have replace != 0 implies selected == replacement by simp;
            have not (replace != 0) implies selected == original by simp;
            have index < index + 1 by simp;
        }
        else {
            step() using {
                index < owner->len;
                0 <= index;
                1 <= owner->len;
                owner->len <= owner->cap;
                replace == 0;
                loadable(old(owner->cap));
                loadable(old(owner->data));
                loadable(old(owner->len));
            }
            have replace != 0 implies selected == replacement by simp;
            have not (replace != 0) implies selected == original by simp;
            have index < index + 1 by simp;
        }
    }
    execute();
    have index < index + 1 by simp;
    frame() using {
    }
    simp();
}

int32 vector_clear(struct vector* owner) {
    consumes nonempty_vector(owner);
    mutable owner->len;
    produces empty_vector(owner);
    ensures result == 0;
    ensures owner->len == 0;
} by {
    unfold(nonempty_vector(owner));
    execute();
    have owner->len == 0 by simp;
    have 1 <= owner->cap by simp;
    have separate(memory(object(owner)), memory(owner->data[0..owner->cap])) by simp;
    fold(empty_vector(owner));
    frame();
    simp();
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
    execute_until(statement(3));
    have owner->len == 0 by simp;
    have owner->cap == capacity by simp;
    unfold(empty_vector(owner));
    have 0 <= owner->len by simp;
    have owner->len <= owner->cap by simp;
    have loadable(owner->data[0..owner->len]) by simp;
    fold(vector_storage(owner));
    have owner->len < owner->cap by simp;
    step() using {
        owner->len < owner->cap;
        loadable(owner->len);
        loadable(owner->cap);
        loadable(owner->data);
    }
    unfold(vector_storage(owner));
    have owner->len == 1 by simp;
    have 1 <= owner->len by simp;
    fold(nonempty_vector(owner));
    have 0 < owner->len by simp;
    step() using {
        0 < owner->len;
    }
    have owner->len == 1 by simp;
    have 0 < owner->len by simp;
    step() using {
        0 < owner->len;
    }
    have owner->len == 1 by simp;
    observe(nonempty_vector(owner));
    have owner->data[0] == replacement by simp;
    have 0 < owner->len by simp;
    step() using {
        0 < owner->len;
        owner->len == 1;
    }
    have observed == owner->data[0] by simp;
    have observed == replacement by simp;
    step() using {
        owner->len == 1;
        observed == replacement;
    }
    step() using {
        observed == replacement;
    }
    simp();
}
