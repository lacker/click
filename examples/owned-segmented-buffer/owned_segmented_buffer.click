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
    consumes owner[0..6];
    consumes first_data[0..first_len];
    consumes second_data[0..second_len];
    mutable owner[0..6];
    produces owned_segmented_buffer(owner);
    ensures result == first_len;
    ensures owner->first_len == first_len;
    ensures owner->second_len == second_len;
    ensures 0 < owner->first_len;
    ensures 0 < owner->second_len;
    ensures owner->first_data == first_data;
    ensures owner->second_data == second_data;
} by {
    execute_rest();
    have 0 <= owner->first_len by { simp(); }
    have 0 <= owner->second_len by { simp(); }
    fold(owned_segment(owner->first_data, owner->first_len));
    fold(owned_segment(owner->second_data, owner->second_len));
    have 1 <= owner->first_len by { simp(); }
    have 1 <= owner->second_len by { simp(); }
    fold(owned_segmented_buffer(owner));
    frame();
    simp();
}

int32 owned_segmented_buffer_get_first(
    struct owned_segmented_buffer* owner,
    int32 index
) {
    requires 0 <= index;
    requires index < owner->first_len;
    views owned_segmented_buffer(owner);
    immutable;
    ensures result == (owner->first_data)[index];
} by {
    observe(owned_segmented_buffer(owner));
    observe(owned_segment(owner->first_data, owner->first_len));
    step using {
        fact 0 <= index;
        fact index < load_int32(owner);
        fact loadable(owner[0..1]);
        fact loadable(owner[2..4]);
        fact loadable(load_int32_pointer((owner + 2))[0..load_int32(owner)]);
    }
    frame();
    simp();
}

int32 owned_segmented_buffer_set_first(
    struct owned_segmented_buffer* owner,
    int32 index,
    int32 value
) {
    requires 0 <= index;
    requires index < owner->first_len;
    owns owned_segmented_buffer(owner);
    mutable (owner->first_data)[index..index + 1];
    ensures result == value;
    ensures (owner->first_data)[index] == value;
    ensures owner->first_len == old(owner->first_len);
    ensures owner->second_len == old(owner->second_len);
    ensures owner->first_data == old(owner->first_data);
    ensures owner->second_data == old(owner->second_data);
} by {
    unfold(owned_segmented_buffer(owner));
    unfold(owned_segment(owner->first_data, owner->first_len));
    execute_step();
    step using {
        fact 0 <= index;
        fact index < load_int32(owner);
        fact loadable(old(owner[0..1]));
        fact loadable(old((owner + 1)[0..1]));
        fact loadable(old((owner + 2)[0..2]));
        fact loadable(old((owner + 4)[0..2]));
        fact 1 <= load_int32(owner);
        fact 1 <= load_int32((owner + 1));
        fact 0 <= load_int32(owner);
    }
    have 0 <= owner->first_len by { simp(); }
    fold(owned_segment(owner->first_data, owner->first_len));
    have 1 <= owner->first_len by { simp(); }
    have 1 <= owner->second_len by { simp(); }
    fold(owned_segmented_buffer(owner));
    have index < index + 1 by { simp(); }
    frame();
    simp();
}

int32 owned_segmented_buffer_set_second(
    struct owned_segmented_buffer* owner,
    int32 index,
    int32 value
) {
    requires 0 <= index;
    requires index < owner->second_len;
    owns owned_segmented_buffer(owner);
    mutable (owner->second_data)[index..index + 1];
    ensures result == value;
    ensures (owner->second_data)[index] == value;
    ensures owner->first_len == old(owner->first_len);
    ensures owner->second_len == old(owner->second_len);
    ensures owner->first_data == old(owner->first_data);
    ensures owner->second_data == old(owner->second_data);
} by {
    unfold(owned_segmented_buffer(owner));
    unfold(owned_segment(owner->second_data, owner->second_len));
    execute_step();
    step using {
        fact 0 <= index;
        fact index < load_int32((owner + 1));
        fact loadable(old(owner[0..1]));
        fact loadable(old((owner + 1)[0..1]));
        fact loadable(old((owner + 2)[0..2]));
        fact loadable(old((owner + 4)[0..2]));
        fact 1 <= load_int32(owner);
        fact 1 <= load_int32((owner + 1));
        fact 0 <= load_int32((owner + 1));
    }
    have 0 <= owner->second_len by { simp(); }
    fold(owned_segment(owner->second_data, owner->second_len));
    have 1 <= owner->first_len by { simp(); }
    have 1 <= owner->second_len by { simp(); }
    fold(owned_segmented_buffer(owner));
    have index < index + 1 by { simp(); }
    frame();
    simp();
}

int32 owned_segmented_buffer_swap(struct owned_segmented_buffer* owner) {
    owns owned_segmented_buffer(owner);
    mutable owner[0..6];
    ensures result == old(owner->second_len);
    ensures owner->first_len == old(owner->second_len);
    ensures owner->second_len == old(owner->first_len);
    ensures 0 < owner->first_len;
    ensures 0 < owner->second_len;
    ensures owner->first_data == old(owner->second_data);
    ensures owner->second_data == old(owner->first_data);
} by {
    unfold(owned_segmented_buffer(owner));
    execute_rest();
    have 1 <= owner->first_len by { simp(); }
    have 1 <= owner->second_len by { simp(); }
    fold(owned_segmented_buffer(owner));
    frame();
    simp();
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
    consumes owner[0..6];
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
    execute_until(statement(3));
    have 0 < owner->first_len by {
        simp();
    }
    have 0 < owner->second_len by {
        simp();
    }
    have owner->first_data == first_data by {
        simp();
    }
    have owner->second_data == second_data by {
        simp();
    }
    step using {
        fact 1 <= first_len;
        fact 1 <= second_len;
        fact loadable(old(owner[0..6]));
        fact loadable(old(first_data[0..first_len]));
        fact loadable(old(second_data[0..second_len]));
        fact separate(memory(owner[read_value..6]), memory(first_data[read_value..first_len]));
        fact separate(memory(owner[read_value..6]), memory(second_data[read_value..second_len]));
        fact separate(memory(first_data[read_value..first_len]), memory(second_data[read_value..second_len]));
        fact ignored == first_len;
        fact *owner == first_len;
        fact *(owner + 1) == second_len;
        fact 0 < load_int32(owner);
        fact 0 < load_int32((owner + 1));
        fact load_int32_pointer((owner + 2)) == first_data;
        fact load_int32_pointer((owner + 4)) == second_data;
    }
    have 0 < owner->second_len by {
        simp();
    }
    have owner->first_data == first_data by {
        simp();
    }
    have owner->second_data == second_data by {
        simp();
    }
    have first_data[0] == first_value by {
        derive(first_data[0] == first_value) using {
            fact at(statement(4).entry, *load_int32_pointer((owner + 2))) == at(statement(4).entry, first_value);
            fact load_int32_pointer((owner + 2)) == first_data;
        }
    }
    step using {
        fact loadable(old(owner[0..6]));
        fact 0 < load_int32((owner + 1));
        fact read_value < *owner;
        fact 1 <= first_len;
        fact 1 <= second_len;
        fact ignored == first_value;
        fact *(owner + 1) == second_len;
        fact *owner == first_len;
        fact first_data[0] == first_value;
        fact load_int32_pointer((owner + 2)) == first_data;
        fact load_int32_pointer((owner + 4)) == second_data;
    }
    transport(at(statement(4).entry, *owner) == at(statement(4).entry, first_len), *owner == first_len) using {
        fact 1 <= second_len;
        fact at(statement(4).entry, *owner) == first_len;
        fact at(statement(4).entry, load_int32_pointer((owner + 4))) == second_data;
    }
    transport(at(statement(4).entry, *(owner + 1)) == at(statement(4).entry, second_len), *(owner + 1) == second_len) using {
        fact 1 <= second_len;
        fact at(statement(4).entry, *(owner + 1)) == second_len;
        fact at(statement(4).entry, load_int32_pointer((owner + 4))) == second_data;
    }
    transport(at(statement(4).entry, read_value) < at(statement(4).entry, *owner), read_value < *owner) using {
        fact read_value < at(statement(4).entry, *owner);
        fact 1 <= second_len;
        fact at(statement(4).entry, load_int32_pointer((owner + 4))) == second_data;
    }
    transport(at(statement(4).entry, 0) < at(statement(4).entry, load_int32((owner + 1))), 0 < load_int32((owner + 1))) using {
        fact 0 < at(statement(4).entry, load_int32((owner + 1)));
        fact at(statement(4).entry, *(owner + 1)) == second_len;
        fact at(statement(4).entry, load_int32_pointer((owner + 4))) == second_data;
    }
    transport(at(statement(4).entry, first_data[0]) == at(statement(4).entry, first_value), first_data[0] == first_value) using {
        fact 1 <= first_len;
        fact 1 <= second_len;
        fact at(statement(4).entry, first_data[0]) == first_value;
        fact at(statement(4).entry, load_int32_pointer((owner + 4))) == second_data;
    }
    transport(at(statement(4).entry, load_int32_pointer((owner + 2))) == at(statement(4).entry, first_data), load_int32_pointer((owner + 2)) == first_data) using {
        fact 1 <= second_len;
        fact at(statement(4).entry, load_int32_pointer((owner + 2))) == first_data;
        fact at(statement(4).entry, load_int32_pointer((owner + 4))) == second_data;
    }
    transport(at(statement(4).entry, load_int32_pointer((owner + 4))) == at(statement(4).entry, second_data), load_int32_pointer((owner + 4)) == second_data) using {
        fact at(statement(4).entry, load_int32_pointer((owner + 4))) == at(statement(4).entry, second_data);
        fact 1 <= second_len;
    }
    have 0 < owner->first_len by {
        simp();
    }
    have owner->first_data == first_data by {
        simp();
    }
    have owner->second_data == second_data by {
        simp();
    }
    have second_data[0] == second_value by {
        derive(second_data[0] == second_value) using {
            fact at(statement(5).entry, *load_int32_pointer((owner + 4))) == at(statement(5).entry, second_value);
            fact load_int32_pointer((owner + 4)) == second_data;
        }
    }
    step using {
        fact 0 < owner->first_len;
        fact loadable(owner[0..1]);
        fact loadable((owner + 2)[0..2]);
        fact owner->first_data == first_data;
        fact first_data[0] == first_value;
    }
    have read_value == first_data[0] by {
        derive(read_value == first_data[0]) using {
            fact at(statement(6).entry, read_value) == at(statement(6).entry, *load_int32_pointer((owner + 2)));
            fact load_int32_pointer((owner + 2)) == first_data;
        }
    }
    apply(int32_equality_transitive(
        read_value,
        first_data[0],
        first_value
    ));
    execute_rest();
    simp();
}
