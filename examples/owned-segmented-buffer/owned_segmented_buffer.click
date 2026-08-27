theorem int32_equality_transitive(first: int32, second: int32, third: int32) {
    requires first == second;
    requires second == third;

    ensures first == third by {
        simp();
    }
}

resource owned_segment(data: int32*, length: int32) {
    owns data[0..length];
    fact 0 <= length;
}

resource owned_segmented_buffer(owner: struct owned_segmented_buffer*) {
    owns owner->first_len;
    owns owner->second_len;
    owns owner->first_data;
    owns owner->second_data;
    contains owned_segment(owner->first_data, owner->first_len);
    contains owned_segment(owner->second_data, owner->second_len);
    fact 1 <= owner->first_len;
    fact 1 <= owner->second_len;
}

verifying "owned_segmented_buffer_init.c";
verifying "owned_segmented_buffer_get_first.c";
verifying "owned_segmented_buffer_set_first.c";
verifying "owned_segmented_buffer_set_second.c";
verifying "owned_segmented_buffer_swap.c";
verifying "owned_segmented_buffer_pipeline.c";

int32 owned_segmented_buffer_init(
    struct owned_segmented_buffer* owner,
    int32 first_data[],
    int32 first_len,
    int32 second_data[],
    int32 second_len
) {
    requires 1 <= first_len;
    requires 1 <= second_len;
    consumes object(owner);
    consumes first_data[0..first_len];
    consumes second_data[0..second_len];
    mutable object(owner);
    produces owned_segmented_buffer(owner);
    ensures result == first_len;
    ensures owner->first_len == first_len;
    ensures owner->second_len == second_len;
    ensures 0 < owner->first_len;
    ensures 0 < owner->second_len;
    ensures owner->first_data == first_data;
    ensures owner->second_data == second_data;
} by {
    step();
    step();
    step();
    step();
    step();
    have 0 <= owner->first_len by {
        apply(int32_positive_is_nonnegative(at(statement(4).entry, first_len))) using {
            at(statement(4).entry, 1) <= at(statement(4).entry, first_len);
        }
        assumption();
    }
    have 0 <= owner->second_len by {
        apply(int32_positive_is_nonnegative(at(statement(4).entry, second_len))) using {
            at(statement(4).entry, 1) <= at(statement(4).entry, second_len);
        }
        assumption();
    }
    fold(owned_segment(owner->first_data, owner->first_len));
    fold(owned_segment(owner->second_data, owner->second_len));
    have 1 <= owner->first_len by {
        assumption();
    }
    have 1 <= owner->second_len by {
        assumption();
    }
    fold(owned_segmented_buffer(owner));
    frame() using {
    }
    have result == first_len by {
        normalize();
    }
    have owner->first_len == first_len by {
        normalize();
    }
    have owner->second_len == second_len by {
        normalize();
    }
    have 0 < owner->first_len by {
        apply(int32_successor_le_implies_lt(0, owner->first_len)) using {
            1 <= owner->first_len;
        }
        assumption();
    }
    have 0 < owner->second_len by {
        apply(int32_successor_le_implies_lt(0, owner->second_len)) using {
            1 <= owner->second_len;
        }
        assumption();
    }
    have owner->first_data == first_data by {
        normalize();
    }
    have owner->second_data == second_data by {
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
}

int32 owned_segmented_buffer_get_first(
    struct owned_segmented_buffer* owner,
    int32 index
) {
    requires 0 <= index;
    requires index < owner->first_len;
    views owned_segmented_buffer(owner);
    immutable;
    ensures result == owner->first_data[index];
} by {
    observe(owned_segmented_buffer(owner));
    observe(owned_segment(owner->first_data, owner->first_len));
    step();
    frame() using {
    }
    have result == owner->first_data[index] by {
        normalize();
    }
    assumption();
}

int32 owned_segmented_buffer_set_first(
    struct owned_segmented_buffer* owner,
    int32 index,
    int32 value
) {
    requires 0 <= index;
    requires index < owner->first_len;
    owns owned_segmented_buffer(owner);
    mutable owner->first_data[index..index + 1];
    ensures result == value;
    ensures owner->first_data[index] == value;
    ensures owner->first_len == old(owner->first_len);
    ensures owner->second_len == old(owner->second_len);
    ensures owner->first_data == old(owner->first_data);
    ensures owner->second_data == old(owner->second_data);
} by {
    unfold(owned_segmented_buffer(owner));
    unfold(owned_segment(owner->first_data, owner->first_len));
    step();
    step();
    have 0 <= owner->first_len by {
        assumption();
    }
    fold(owned_segment(owner->first_data, owner->first_len));
    have 1 <= owner->first_len by {
        assumption();
    }
    have 1 <= owner->second_len by {
        assumption();
    }
    fold(owned_segmented_buffer(owner));
    have index < (index + 1) by {
        apply(int32_increment_strictly_increases(at(statement(1).entry, index), at(statement(1).entry, owner->first_len))) using {
            at(statement(1).entry, index) < at(statement(1).entry, owner->first_len);
        }
        assumption();
    }
    have index <= index by {
        normalize();
    }
    have index < (index + 1) by {
        apply(int32_increment_strictly_increases(at(statement(1).entry, index), at(statement(1).entry, owner->first_len))) using {
            at(statement(1).entry, index) < at(statement(1).entry, owner->first_len);
        }
        assumption();
    }
    frame() using {
        at(statement(1).entry, 0) <= at(statement(1).entry, index);
        at(statement(1).entry, index) < at(statement(1).entry, owner->first_len);
        index <= index;
        index < (index + 1);
    }
    have result == value by {
        normalize();
    }
    have owner->first_data[index] == value by {
        normalize();
    }
    have owner->first_len == old(owner->first_len) by {
        normalize();
    }
    have owner->second_len == old(owner->second_len) by {
        normalize();
    }
    have owner->first_data == old(owner->first_data) by {
        normalize();
    }
    have owner->second_data == old(owner->second_data) by {
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

int32 owned_segmented_buffer_set_second(
    struct owned_segmented_buffer* owner,
    int32 index,
    int32 value
) {
    requires 0 <= index;
    requires index < owner->second_len;
    owns owned_segmented_buffer(owner);
    mutable owner->second_data[index..index + 1];
    ensures result == value;
    ensures owner->second_data[index] == value;
    ensures owner->first_len == old(owner->first_len);
    ensures owner->second_len == old(owner->second_len);
    ensures owner->first_data == old(owner->first_data);
    ensures owner->second_data == old(owner->second_data);
} by {
    unfold(owned_segmented_buffer(owner));
    unfold(owned_segment(owner->second_data, owner->second_len));
    step();
    step();
    have 0 <= owner->second_len by {
        assumption();
    }
    fold(owned_segment(owner->second_data, owner->second_len));
    have 1 <= owner->first_len by {
        assumption();
    }
    have 1 <= owner->second_len by {
        assumption();
    }
    fold(owned_segmented_buffer(owner));
    have index < (index + 1) by {
        apply(int32_increment_strictly_increases(at(statement(1).entry, index), at(statement(1).entry, owner->second_len))) using {
            at(statement(1).entry, index) < at(statement(1).entry, owner->second_len);
        }
        assumption();
    }
    have index <= index by {
        normalize();
    }
    have index < (index + 1) by {
        apply(int32_increment_strictly_increases(at(statement(1).entry, index), at(statement(1).entry, owner->second_len))) using {
            at(statement(1).entry, index) < at(statement(1).entry, owner->second_len);
        }
        assumption();
    }
    frame() using {
        at(statement(1).entry, 0) <= at(statement(1).entry, index);
        at(statement(1).entry, index) < at(statement(1).entry, owner->second_len);
        index <= index;
        index < (index + 1);
    }
    have result == value by {
        normalize();
    }
    have owner->second_data[index] == value by {
        normalize();
    }
    have owner->first_len == old(owner->first_len) by {
        normalize();
    }
    have owner->second_len == old(owner->second_len) by {
        normalize();
    }
    have owner->first_data == old(owner->first_data) by {
        normalize();
    }
    have owner->second_data == old(owner->second_data) by {
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

int32 owned_segmented_buffer_swap(struct owned_segmented_buffer* owner) {
    owns owned_segmented_buffer(owner);
    mutable object(owner);
    ensures result == old(owner->second_len);
    ensures owner->first_len == old(owner->second_len);
    ensures owner->second_len == old(owner->first_len);
    ensures 0 < owner->first_len;
    ensures 0 < owner->second_len;
    ensures owner->first_data == old(owner->second_data);
    ensures owner->second_data == old(owner->first_data);
} by {
    unfold(owned_segmented_buffer(owner));
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    have 1 <= owner->first_len by {
        assumption();
    }
    have 1 <= owner->second_len by {
        assumption();
    }
    fold(owned_segmented_buffer(owner));
    frame() using {
    }
    have result == old(owner->second_len) by {
        normalize();
    }
    have owner->first_len == old(owner->second_len) by {
        normalize();
    }
    have owner->second_len == old(owner->first_len) by {
        normalize();
    }
    have 0 < owner->first_len by {
        apply(int32_successor_le_implies_lt(0, owner->first_len)) using {
            1 <= owner->first_len;
        }
        assumption();
    }
    have 0 < owner->second_len by {
        apply(int32_successor_le_implies_lt(0, owner->second_len)) using {
            1 <= owner->second_len;
        }
        assumption();
    }
    have owner->first_data == old(owner->second_data) by {
        normalize();
    }
    have owner->second_data == old(owner->first_data) by {
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
}

int32 owned_segmented_buffer_pipeline(
    struct owned_segmented_buffer* owner,
    int32 first_data[],
    int32 first_len,
    int32 second_data[],
    int32 second_len,
    int32 first_value,
    int32 second_value
) {
    requires 1 <= first_len;
    requires 1 <= second_len;
    consumes object(owner);
    consumes first_data[0..first_len];
    consumes second_data[0..second_len];
    produces owned_segmented_buffer(owner);
    ensures owner->first_len == first_len;
    ensures owner->second_len == second_len;
    ensures owner->first_data == first_data;
    ensures owner->second_data == second_data;
    ensures first_data[0] == first_value;
    ensures second_data[0] == second_value;
    ensures result == first_value;
} by {
    step();
    step();
    step();
    have ignored == first_len by {
        assumption();
    }
    have 0 < owner->first_len by {
        assumption();
    }
    have 0 < owner->second_len by {
        assumption();
    }
    have owner->first_data == first_data by {
        assumption();
    }
    have owner->second_data == second_data by {
        assumption();
    }
    step();
    have 0 < owner->second_len by {
        assumption();
    }
    have owner->first_data == first_data by {
        assumption();
    }
    have owner->second_data == second_data by {
        assumption();
    }
    have at(statement(4).entry, first_data[0]) == at(statement(4).entry, first_value) by {
        rewrite(at(statement(4).entry, first_value) == at(statement(4).entry, owner->first_data[0]));
        rewrite(at(statement(4).entry, owner->first_data) == at(statement(4).entry, first_data));
        normalize();
    }
    transport(at(statement(4).entry, first_data[0]) == at(statement(4).entry, first_value), first_data[0] == first_value) using {
        at(statement(4).entry, first_data[0]) == at(statement(4).entry, first_value);
    }
    step();
    transport(at(statement(4).entry, owner->first_len) == at(statement(4).entry, first_len), owner->first_len == first_len) using {
        1 <= second_len;
        at(statement(4).entry, owner->first_len) == first_len;
        at(statement(4).entry, owner->second_data) == second_data;
    }
    transport(at(statement(4).entry, owner->second_len) == at(statement(4).entry, second_len), owner->second_len == second_len) using {
        1 <= second_len;
        at(statement(4).entry, owner->second_len) == second_len;
        at(statement(4).entry, owner->second_data) == second_data;
    }
    transport(at(statement(4).entry, 0) < at(statement(4).entry, owner->first_len), 0 < owner->first_len) using {
        0 < at(statement(4).entry, owner->first_len);
        1 <= second_len;
        at(statement(4).entry, owner->second_data) == second_data;
    }
    transport(at(statement(4).entry, 0) < at(statement(4).entry, owner->second_len), 0 < owner->second_len) using {
        0 < at(statement(4).entry, owner->second_len);
        at(statement(4).entry, owner->second_len) == second_len;
        at(statement(4).entry, owner->second_data) == second_data;
    }
    transport(at(statement(4).entry, first_data[0]) == at(statement(4).entry, first_value), first_data[0] == first_value) using {
        1 <= first_len;
        1 <= second_len;
        at(statement(4).entry, first_data[0]) == first_value;
        at(statement(4).entry, owner->second_data) == second_data;
    }
    transport(at(statement(4).entry, owner->first_data) == at(statement(4).entry, first_data), owner->first_data == first_data) using {
        1 <= second_len;
        at(statement(4).entry, owner->first_data) == first_data;
        at(statement(4).entry, owner->second_data) == second_data;
    }
    transport(at(statement(4).entry, owner->second_data) == at(statement(4).entry, second_data), owner->second_data == second_data) using {
        at(statement(4).entry, owner->second_data) == at(statement(4).entry, second_data);
        1 <= second_len;
    }
    have 0 < owner->first_len by {
        assumption();
    }
    have owner->first_data == first_data by {
        assumption();
    }
    have owner->second_data == second_data by {
        assumption();
    }
    have at(statement(5).entry, second_data[0]) == at(statement(5).entry, second_value) by {
        rewrite(at(statement(5).entry, second_value) == at(statement(5).entry, owner->second_data[0]));
        rewrite(at(statement(5).entry, owner->second_data) == at(statement(5).entry, second_data));
        normalize();
    }
    transport(at(statement(5).entry, second_data[0]) == at(statement(5).entry, second_value), second_data[0] == second_value) using {
        at(statement(5).entry, second_data[0]) == at(statement(5).entry, second_value);
    }
    step();
    have c(result) == first_data[0] by {
        rewrite(at(statement(6).entry, c(result)) == at(statement(6).entry, owner->first_data[0]));
        rewrite(owner->first_data == first_data);
        normalize();
    }
    apply(int32_equality_transitive(c(result), first_data[0], first_value)) using {
        c(result) == first_data[0];
        *first_data == first_value;
    }
    step();
    have owner->first_len == first_len by {
        assumption();
    }
    have owner->second_len == second_len by {
        assumption();
    }
    have owner->first_data == first_data by {
        assumption();
    }
    have owner->second_data == second_data by {
        assumption();
    }
    have first_data[0] == first_value by {
        assumption();
    }
    have second_data[0] == second_value by {
        assumption();
    }
    have result == first_value by {
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
}
