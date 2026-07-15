resource empty_vector(owner: struct vector*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns (owner->data)[0..owner->cap];
    fact owner->len == 0;
    fact 1 <= owner->cap;
    fact separate(memory(owner[0..4]), memory((owner->data)[0..owner->cap]));
}

resource vector(owner: struct vector*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns (owner->data)[0..owner->cap];
    fact 1 <= owner->len;
    fact owner->len <= owner->cap;
    fact separate(memory(owner[0..4]), memory((owner->data)[0..owner->cap]));
}

verifying "vector_init.c";
verifying "vector_len.c";
verifying "vector_get.c";
verifying "vector_set.c";
verifying "vector_push.c";
verifying "vector_clear.c";
verifying "vector_pipeline.c";

int32 vector_init(struct vector* owner, int32 data[], int32 capacity) {
    requires 1 <= capacity;
    consumes owner[0..4];
    consumes data[0..capacity];
    mutable_field(owner->len), (owner->cap), (owner->data) by frame;

    produces empty_vector(owner) by {
        execute_rest();
        fold(empty_vector(owner));
    }

    ensures result == 0 by auto;
    ensures owner->len == 0 by auto;
    ensures owner->cap == capacity by auto;
    ensures owner->data == data by auto;
}

int32 vector_len(struct vector* owner) {
    views vector(owner);

    ensures result == owner->len by auto;
}

int32 vector_get(struct vector* owner, int32 index) {
    requires 0 <= index;
    requires index < owner->len;
    views vector(owner);

    ensures result == (owner->data)[index] by auto;
}

int32 vector_set(struct vector* owner, int32 index, int32 value) {
    requires 0 <= index;
    requires index < owner->len;
    mutable (owner->data)[index..index + 1] by {
        unfold(vector(owner));
        execute_rest();
        frame();
    }

    owns vector(owner) by {
        unfold(vector(owner));
        execute_rest();
        fold(vector(owner));
    }

    ensures result == value by {
        unfold(vector(owner));
        execute_rest();
        fold(vector(owner));
        simp();
    }
    ensures (owner->data)[index] == value by {
        unfold(vector(owner));
        execute_rest();
        fold(vector(owner));
        simp();
    }
    ensures owner->len == old(owner->len) by {
        unfold(vector(owner));
        execute_rest();
        simp();
    }
}

int32 vector_push(struct vector* owner, int32 value) {
    consumes empty_vector(owner);
    mutable owner[0..1], (owner->data)[0..1] by {
        unfold(empty_vector(owner));
        have owner->len < owner->cap by simp;
        execute_until(statement(8));
        have owner->len == 1 by simp;
        execute_rest();
        frame();
    }

    produces vector(owner) by {
        unfold(empty_vector(owner));
        have owner->len < owner->cap by simp;
        execute_until(statement(8));
        have owner->len == 1 by simp;
        fold(vector(owner));
        execute_rest();
    }

    ensures result == 1 by {
        unfold(empty_vector(owner));
        have owner->len < owner->cap by simp;
        execute_until(statement(8));
        have owner->len == 1 by simp;
        fold(vector(owner));
        execute_rest();
        simp();
    }
    ensures owner->len == 1 by {
        unfold(empty_vector(owner));
        have owner->len < owner->cap by simp;
        execute_until(statement(8));
        have owner->len == 1 by simp;
        fold(vector(owner));
        execute_rest();
        simp();
    }
    ensures (owner->data)[0] == value by {
        unfold(empty_vector(owner));
        have owner->len < owner->cap by simp;
        execute_until(statement(8));
        have owner->len == 1 by simp;
        fold(vector(owner));
        execute_rest();
        simp();
    }
}

int32 vector_clear(struct vector* owner) {
    consumes vector(owner);
    mutable_field(owner->len) by {
        unfold(vector(owner));
        execute_rest();
        frame();
    }

    produces empty_vector(owner) by {
        unfold(vector(owner));
        execute_rest();
        fold(empty_vector(owner));
    }

    ensures result == 0 by {
        unfold(vector(owner));
        execute_rest();
        fold(empty_vector(owner));
        simp();
    }
    ensures owner->len == 0 by {
        unfold(vector(owner));
        execute_rest();
        fold(empty_vector(owner));
        simp();
    }
}

int32 vector_pipeline(
    struct vector* owner,
    int32 data[],
    int32 capacity,
    int32 first,
    int32 replacement
) {
    requires 1 <= capacity;
    consumes owner[0..4];
    consumes data[0..capacity];

    produces empty_vector(owner) by {
        execute_step();
        execute_step();
        execute_step();
        execute_step();
        execute_step();
        execute_step();
        observe(vector(owner));
        execute_step();
        execute_step();
        execute_step();
    }

    ensures result == replacement by {
        execute_step();
        execute_step();
        execute_step();
        execute_step();
        execute_step();
        execute_step();
        observe(vector(owner));
        execute_step();
        execute_step();
        execute_step();
        simp();
    }
}
