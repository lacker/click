authorized resource pool_slot(pool: struct pool*) {}
authorized resource pool_object(pool: struct pool*, object: struct object*) { owns *object; }
resource pool_storage(pool: struct pool*) {
    owns *pool;
    owns authority(pool_slot(pool));
    owns authority(pool_object(pool, _));
}
resource pool_control(pool: struct pool*) {
    owns *pool;
    owns authority(pool_slot(pool));
    owns authority(pool_object(pool, _));
    fact 0 <= pool->checked_out;
    fact pool->checked_out == count(pool_object(pool, _));
    fact pool->capacity == pool->checked_out + count(pool_slot(pool));
}
theorem pool_checkout_increment_bound(capacity: int32, used: int32, available: int32) {
    requires 0 <= used;
    requires 1 <= available;
    requires capacity == used + available;
    requires defined(used + available);
    ensures to_integer(used) + 1 <= 2147483647 by auto;
}
theorem pool_shrink_sum_defined(capacity: int32, used: int32, available: int32, amount: int32) {
    requires 0 <= used;
    requires 0 <= amount;
    requires amount <= available;
    requires capacity == used + available;
    requires defined(used + available);
    ensures defined(used + (available - amount)) by auto;
}
theorem pool_shrink_conservation(capacity: int32, used: int32, available: int32, amount: int32) {
    requires 0 <= used;
    requires 0 <= amount;
    requires amount <= available;
    requires capacity == used + available;
    requires defined(used + available);
    requires defined(capacity - amount);
    ensures capacity - amount == used + (available - amount) by auto;
}
theorem pool_grow_slots_defined(capacity: int32, used: int32, available: int32, amount: int32) {
    requires 0 <= used;
    requires 0 <= available;
    requires 0 <= amount;
    requires capacity == used + available;
    requires defined(used + available);
    requires defined(capacity + amount);
    ensures defined(available + amount) by auto;
}
theorem pool_grow_conservation(capacity: int32, used: int32, available: int32, amount: int32) {
    requires 0 <= used;
    requires 0 <= available;
    requires 0 <= amount;
    requires capacity == used + available;
    requires defined(used + available);
    requires defined(capacity + amount);
    ensures defined(used + (available + amount)) and
        capacity + amount == used + (available + amount) by auto;
}
predicate valid_pool(pool: struct pool*) {
    0 <= pool->checked_out and
    pool->checked_out == count(pool_object(pool, _)) and
    pool->capacity == pool->checked_out + count(pool_slot(pool))
}
verifying "pool_init.c";
verifying "pool_destroy.c";
verifying "pool_zero_pipeline.c";
verifying "pool_checkout.c";
verifying "pool_return.c";
verifying "pool_transfer.c";
verifying "pool_transfer_pipeline.c";
verifying "pool_pipeline.c";
verifying "pool_grow.c";
verifying "pool_shrink.c";
verifying "pool_resize_pipeline.c";
void pool_init(struct pool* pool, int32 capacity) {
    consumes pool_storage(pool);
    requires 0 <= capacity;
    requires count(pool_slot(pool)) == 0;
    requires count(pool_object(pool, _)) == 0;
    produces pool_control(pool);
    produces capacity of pool_slot(pool);
    ensures pool->capacity == capacity;
    ensures pool->checked_out == 0;
    ensures count(pool_object(pool, _)) == 0;
    ensures valid_pool(pool);
} by {
    unfold(pool_storage(pool));
    step(); step();
    fold(capacity of pool_slot(pool));
    fold(pool_control(pool));
    execute(); unfold(valid_pool); simp();
}
void pool_destroy(struct pool* pool) {
    consumes pool_control(pool);
    consumes pool->capacity of pool_slot(pool);
    requires pool->checked_out == 0;
    produces *pool;
    ensures pool->checked_out == 0;
    ensures pool->capacity == 0;
    ensures count(pool_slot(pool)) == 0;
    ensures count(pool_object(pool, _)) == 0;
    ensures valid_pool(pool);
} by {
    unfold(pool_control(pool));
    unfold(pool->capacity of pool_slot(pool));
    have count(pool_slot(pool)) == 0;
    step();
    unfold(authority(pool_slot(pool)));
    unfold(authority(pool_object(pool, _)));
    execute(); unfold(valid_pool); simp();
}
void pool_zero_pipeline(struct pool* pool) {
    consumes pool_storage(pool);
    requires count(pool_slot(pool)) == 0;
    requires count(pool_object(pool, _)) == 0;
    produces *pool;
    ensures pool->checked_out == 0;
    ensures pool->capacity == 0;
    ensures count(pool_slot(pool)) == 0;
    ensures count(pool_object(pool, _)) == 0;
    ensures valid_pool(pool);
} by {
    step();
    unfold(pool_control(pool));
    fold(pool_control(pool));
    step();
    execute(); unfold(valid_pool); simp();
}

void pool_checkout(struct pool* pool, struct object* object) {
    owns pool_control(pool);
    consumes pool_slot(pool);
    consumes *object;
    produces pool_object(pool, object);
    ensures count(pool_slot(pool)) == old(count(pool_slot(pool))) - 1;
    ensures count(pool_object(pool, _)) == old(count(pool_object(pool, _))) + 1;
    ensures pool->checked_out == old(pool->checked_out) + 1;
    ensures pool->capacity == old(pool->capacity);
    ensures valid_pool(pool);
    ensures object->value == old(object->value);
} by {
    open(pool_control(pool)) {
        apply(int32_move_one_from_right_to_left_preserves_sum(
            pool->capacity, pool->checked_out, count(pool_slot(pool))
        )) using {
            0 <= pool->checked_out;
            1 <= count(pool_slot(pool));
            pool->capacity == pool->checked_out + count(pool_slot(pool));
        }
        have defined(pool->checked_out + count(pool_slot(pool)));
        apply(pool_checkout_increment_bound(pool->capacity, pool->checked_out, count(pool_slot(pool)))) using {
            1 <= count(pool_slot(pool));
            0 <= pool->checked_out;
            pool->capacity == pool->checked_out + count(pool_slot(pool));
            defined(pool->checked_out + count(pool_slot(pool)));
        }
        have to_integer(pool->checked_out) + 1 >= -2147483648 by auto;
        apply(int32_add_defined_by_integer_bounds(pool->checked_out, 1)) using {
            to_integer(pool->checked_out) + 1 <= 2147483647;
            to_integer(pool->checked_out) + 1 >= -2147483648;
        }
        have defined(count(pool_object(pool, _)) + 1) by auto;
        unfold(pool_slot(pool));
        step();
        fold(pool_object(pool, object));
    }
    execute(); unfold(valid_pool); simp();
}

void pool_return(struct pool* pool, struct object* object) {
    owns pool_control(pool);
    requires count(pool_object(pool, object)) == 1;
    consumes pool_object(pool, object);
    produces *object;
    produces pool_slot(pool);
    ensures count(pool_slot(pool)) == old(count(pool_slot(pool))) + 1;
    ensures count(pool_object(pool, _)) == old(count(pool_object(pool, _))) - 1;
    ensures pool->checked_out == old(pool->checked_out) - 1;
    ensures pool->capacity == old(pool->capacity);
    ensures defined(pool->checked_out + count(pool_slot(pool)));
    ensures pool->capacity == pool->checked_out + count(pool_slot(pool));
    ensures valid_pool(pool);
    ensures object->value == old(object->value);
} by {
    open(pool_control(pool)) {
        have 1 <= pool->checked_out by auto;
        have pool->capacity == count(pool_slot(pool)) + pool->checked_out;
        apply(int32_move_one_from_right_to_left_preserves_sum(
            pool->capacity, count(pool_slot(pool)), pool->checked_out
        )) using {
            0 <= count(pool_slot(pool));
            1 <= pool->checked_out;
            pool->capacity == count(pool_slot(pool)) + pool->checked_out;
        }
        have defined(pool->checked_out + count(pool_slot(pool)));
        apply(int32_add_to_integer(pool->checked_out, count(pool_slot(pool)))) using {
            defined(pool->checked_out + count(pool_slot(pool)));
        }
        have to_integer(pool->capacity) == to_integer(pool->checked_out) + to_integer(count(pool_slot(pool))) by auto;
        have 0 <= to_integer(count(pool_slot(pool))) by {
            apply(int32_less_equal_to_integer(0, count(pool_slot(pool)))) using { 0 <= count(pool_slot(pool)); }
            simp();
        }
        have defined(count(pool_slot(pool)) + 1) by auto;
        unfold(pool_object(pool, object));
        step();
        fold(pool_slot(pool));
    }
    execute(); unfold(valid_pool); simp();
}

void pool_pipeline(struct pool* pool, struct object* first, struct object* second) {
    consumes pool_storage(pool);
    requires count(pool_slot(pool)) == 0;
    requires count(pool_object(pool, _)) == 0;
    owns *first;
    owns *second;
    produces *pool;
    ensures pool->checked_out == 0;
    ensures pool->capacity == 0;
    ensures count(pool_slot(pool)) == 0;
    ensures count(pool_object(pool, _)) == 0;
    ensures first->value == 11;
    ensures second->value == 22;
    ensures valid_pool(pool);
} by {
    step();
    have defined(count(pool_object(pool, _)) + 1);
    step();
    have defined(count(pool_object(pool, _)) + 1);
    step();
    open(pool_object(pool, first)) { step(); }
    open(pool_object(pool, second)) { step(); }
    step();
    step();
    unfold(pool_control(pool));
    fold(pool_control(pool));
    step();
    execute(); unfold(valid_pool); simp();
}

void pool_shrink(struct pool* pool, int32 amount) {
    owns pool_control(pool);
    consumes amount of pool_slot(pool);
    requires 0 <= amount;
    requires amount <= count(pool_slot(pool));
    requires defined(pool->capacity - amount);
    ensures pool->capacity == old(pool->capacity) - amount;
    ensures pool->checked_out == old(pool->checked_out);
    ensures count(pool_slot(pool)) == old(count(pool_slot(pool))) - amount;
    ensures count(pool_object(pool, _)) == old(count(pool_object(pool, _)));
    ensures valid_pool(pool);
} by {
    open(pool_control(pool)) {
        have defined(pool->checked_out + count(pool_slot(pool)));
        apply(pool_shrink_sum_defined(pool->capacity, pool->checked_out, count(pool_slot(pool)), amount)) using {
            0 <= pool->checked_out;
            0 <= amount;
            amount <= count(pool_slot(pool));
            pool->capacity == pool->checked_out + count(pool_slot(pool));
            defined(pool->checked_out + count(pool_slot(pool)));
        }
        apply(pool_shrink_conservation(pool->capacity, pool->checked_out, count(pool_slot(pool)), amount)) using {
            0 <= pool->checked_out;
            0 <= amount;
            amount <= count(pool_slot(pool));
            pool->capacity == pool->checked_out + count(pool_slot(pool));
            defined(pool->checked_out + count(pool_slot(pool)));
            defined(pool->capacity - amount);
        }
        unfold(amount of pool_slot(pool));
        step();
    }
    execute(); unfold(valid_pool); simp();
}

void pool_resize_pipeline(struct pool* pool) {
    consumes pool_storage(pool);
    requires count(pool_slot(pool)) == 0;
    requires count(pool_object(pool, _)) == 0;
    produces *pool;
    ensures pool->checked_out == 0;
    ensures pool->capacity == 0;
    ensures count(pool_slot(pool)) == 0;
    ensures count(pool_object(pool, _)) == 0;
    ensures valid_pool(pool);
} by {
    step();
    step();
    unfold(pool_control(pool));
    fold(pool_control(pool));
    step();
    execute(); unfold(valid_pool); simp();
}

void pool_grow(struct pool* pool, int32 amount) {
    owns pool_control(pool);
    requires 0 <= amount;
    requires defined(pool->capacity + amount);
    produces amount of pool_slot(pool);
    ensures pool->capacity == old(pool->capacity) + amount;
    ensures pool->checked_out == old(pool->checked_out);
    ensures count(pool_slot(pool)) == old(count(pool_slot(pool))) + amount;
    ensures count(pool_object(pool, _)) == old(count(pool_object(pool, _)));
    ensures valid_pool(pool);
} by {
    open(pool_control(pool)) {
        have defined(pool->checked_out + count(pool_slot(pool)));
        apply(pool_grow_slots_defined(pool->capacity, pool->checked_out, count(pool_slot(pool)), amount)) using {
            0 <= pool->checked_out; 0 <= count(pool_slot(pool)); 0 <= amount;
            pool->capacity == pool->checked_out + count(pool_slot(pool));
            defined(pool->checked_out + count(pool_slot(pool))); defined(pool->capacity + amount);
        }
        apply(pool_grow_conservation(pool->capacity, pool->checked_out, count(pool_slot(pool)), amount)) using {
            0 <= pool->checked_out; 0 <= count(pool_slot(pool)); 0 <= amount;
            pool->capacity == pool->checked_out + count(pool_slot(pool));
            defined(pool->checked_out + count(pool_slot(pool))); defined(pool->capacity + amount);
        }
        step();
        fold(amount of pool_slot(pool));
    }
    execute(); unfold(valid_pool); simp();
}

void pool_transfer(struct pool* source, struct pool* destination, struct object* object) {
    requires source != destination;
    owns pool_control(source);
    owns pool_control(destination);
    requires count(pool_object(source, object)) == 1;
    requires count(pool_object(destination, object)) == 0;
    consumes pool_object(source, object);
    consumes pool_slot(destination);
    produces pool_object(destination, object);
    produces pool_slot(source);
    ensures count(pool_object(source, _)) == old(count(pool_object(source, _))) - 1;
    ensures count(pool_object(destination, _)) == old(count(pool_object(destination, _))) + 1;
    ensures count(pool_slot(source)) == old(count(pool_slot(source))) + 1;
    ensures count(pool_slot(destination)) == old(count(pool_slot(destination))) - 1;
    ensures source->checked_out == old(source->checked_out) - 1;
    ensures destination->checked_out == old(destination->checked_out) + 1;
    ensures source->capacity == old(source->capacity);
    ensures destination->capacity == old(destination->capacity);
    ensures object->value == old(object->value);
    ensures valid_pool(source);
    ensures valid_pool(destination);
} by {
    open(pool_control(source)) {
        open(pool_control(destination)) {
            have 1 <= source->checked_out by auto;
            have source->capacity == count(pool_slot(source)) + source->checked_out;
            apply(int32_move_one_from_right_to_left_preserves_sum(
                source->capacity, count(pool_slot(source)), source->checked_out
            )) using {
                0 <= count(pool_slot(source));
                1 <= source->checked_out;
                source->capacity == count(pool_slot(source)) + source->checked_out;
            }
            have defined(source->checked_out + count(pool_slot(source)));
            apply(int32_add_to_integer(source->checked_out, count(pool_slot(source)))) using {
                defined(source->checked_out + count(pool_slot(source)));
            }
            have to_integer(source->capacity) == to_integer(source->checked_out) + to_integer(count(pool_slot(source))) by auto;
            have 0 <= to_integer(count(pool_slot(source))) by {
                apply(int32_less_equal_to_integer(0, count(pool_slot(source)))) using { 0 <= count(pool_slot(source)); }
                simp();
            }
            have defined(count(pool_slot(source)) + 1) by auto;
            apply(int32_move_one_from_right_to_left_preserves_sum(
                destination->capacity, destination->checked_out, count(pool_slot(destination))
            )) using {
                0 <= destination->checked_out;
                1 <= count(pool_slot(destination));
                destination->capacity == destination->checked_out + count(pool_slot(destination));
            }
            have defined(destination->checked_out + count(pool_slot(destination)));
            apply(pool_checkout_increment_bound(destination->capacity, destination->checked_out, count(pool_slot(destination)))) using {
                1 <= count(pool_slot(destination));
                0 <= destination->checked_out;
                destination->capacity == destination->checked_out + count(pool_slot(destination));
                defined(destination->checked_out + count(pool_slot(destination)));
            }
            have to_integer(destination->checked_out) + 1 >= -2147483648 by auto;
            apply(int32_add_defined_by_integer_bounds(destination->checked_out, 1)) using {
                to_integer(destination->checked_out) + 1 <= 2147483647;
                to_integer(destination->checked_out) + 1 >= -2147483648;
            }
            have defined(count(pool_object(destination, _)) + 1) by auto;
            unfold(pool_object(source, object));
            unfold(pool_slot(destination));
            step();
            step();
            fold(pool_object(destination, object));
            fold(pool_slot(source));
        }
    }
    execute(); unfold(valid_pool); simp();
}

void pool_transfer_pipeline(struct pool* source, struct pool* destination, struct object* object) {
    requires source != destination;
    consumes pool_storage(source);
    consumes pool_storage(destination);
    consumes *object;
    requires count(pool_slot(source)) == 0;
    requires count(pool_slot(destination)) == 0;
    requires count(pool_object(source, _)) == 0;
    requires count(pool_object(destination, _)) == 0;
    produces pool_control(source);
    produces pool_control(destination);
    produces pool_object(destination, object);
    produces pool_slot(source);
    ensures valid_pool(source);
    ensures valid_pool(destination);
    ensures source->checked_out == 0;
    ensures source->capacity == 1;
    ensures destination->checked_out == 1;
    ensures destination->capacity == 1;
    ensures count(pool_object(source, _)) == 0;
    ensures count(pool_object(destination, _)) == 1;
    ensures count(pool_slot(source)) == 1;
    ensures count(pool_slot(destination)) == 0;
    ensures object->value == old(object->value);
} by {
    open(pool_storage(source)) {
        open(pool_storage(destination)) {
        }
    }
    step();
    open(pool_control(source)) { step(); }
    have defined(count(pool_object(source, _)) + 1);
    open(pool_control(destination)) { step(); }
    have defined(count(pool_object(destination, _)) + 1);
    step();
    execute(); unfold(valid_pool); simp();
}
