resource pool_object(
    pool: struct pool*,
    object: struct object*
) {
    owns object(object);
}

predicate valid_pool(pool: struct pool*) {
    0 <= pool->checked_out and
    pool->checked_out <= pool->capacity and
    pool->checked_out == count(pool_object(pool, _))
}

verifying "pool_init.c";
verifying "pool_checkout.c";
verifying "pool_transfer.c";
verifying "pool_transfer_pipeline.c";
verifying "pool_return.c";
verifying "pool_destroy.c";
verifying "pool_pipeline.c";

void pool_init(struct pool* pool, int32 capacity) {
    requires 0 <= capacity;
    owns object(pool);
    mutable pool->checked_out, pool->capacity;

    ensures valid_pool(pool);
    ensures pool->capacity == capacity;
} by {
    execute();
    have valid_pool(pool) by {
        unfold(valid_pool);
        simp();
    }
    frame();
    simp();
}

void pool_checkout(struct pool* pool, struct object* object) {
    requires valid_pool(pool);
    requires pool->checked_out < pool->capacity;
    owns object(pool);
    consumes object(object);
    mutable pool->checked_out;
    produces pool_object(pool, object);

    ensures valid_pool(pool);
} by {
    unfold(valid_pool);
    execute();
    fold(pool_object(pool, object));
    have valid_pool(pool) by {
        unfold(valid_pool);
        simp();
    }
    frame();
    simp();
}

void pool_return(struct pool* pool, struct object* object) {
    requires valid_pool(pool);
    requires count(pool_object(pool, object)) == 1;
    owns object(pool);
    consumes pool_object(pool, object);
    mutable pool->checked_out;
    produces object(object);

    ensures valid_pool(pool);
} by {
    unfold(valid_pool);
    unfold(pool_object(pool, object));
    execute();
    frame();
    simp();
}

void pool_transfer(
    struct pool* source,
    struct pool* destination,
    struct object* object
) {
    requires source != destination;
    requires valid_pool(source);
    requires valid_pool(destination);
    requires count(pool_object(source, object)) == 1;
    requires count(pool_object(destination, object)) == 0;
    requires destination->checked_out < destination->capacity;
    owns object(source);
    owns object(destination);
    consumes pool_object(source, object);
    mutable source->checked_out, destination->checked_out;
    produces pool_object(destination, object);

    ensures valid_pool(source);
    ensures valid_pool(destination);
} by {
    unfold(valid_pool);
    unfold(pool_object(source, object));
    step() using {
        source != destination;
        count(pool_object(source, object)) == 1;
        count(pool_object(destination, object)) == 0;
        destination->checked_out < destination->capacity;
        loadable(source[0..2]);
        loadable(destination[0..2]);
        loadable(object[0..1]);
        0 <= source->checked_out;
        source->checked_out <= source->capacity;
        source->checked_out == count(pool_object(source, _));
        0 <= destination->checked_out;
        destination->checked_out <= destination->capacity;
        destination->checked_out == count(pool_object(destination, _));
    }
    step() using {
        source != destination;
        count(pool_object(source, object)) == 1;
        count(pool_object(destination, object)) == 0;
        destination->checked_out < destination->capacity;
        loadable(old(source[0..2]));
        loadable(old(destination[0..2]));
        loadable(old(object[0..1]));
        at(statement(0).entry, 0) <= at(statement(0).entry, source->checked_out);
        at(statement(0).entry, source->checked_out) <= at(statement(0).entry, source->capacity);
        at(statement(0).entry, source->checked_out) == at(statement(0).entry, count(pool_object(source, _)));
        0 <= destination->checked_out;
        destination->checked_out <= destination->capacity;
        destination->checked_out == count(pool_object(destination, _));
    }
    step() using {
        source != destination;
        count(pool_object(source, object)) == 1;
        count(pool_object(destination, object)) == 0;
        at(statement(1).entry, destination->checked_out) < at(statement(1).entry, destination->capacity);
        loadable(old(source[0..2]));
        loadable(old(destination[0..2]));
        loadable(old(object[0..1]));
        at(statement(0).entry, 0) <= at(statement(0).entry, source->checked_out);
        at(statement(0).entry, source->checked_out) <= at(statement(0).entry, source->capacity);
        at(statement(0).entry, source->checked_out) == at(statement(0).entry, count(pool_object(source, _)));
        at(statement(1).entry, 0) <= at(statement(1).entry, destination->checked_out);
        at(statement(1).entry, destination->checked_out) <= at(statement(1).entry, destination->capacity);
        at(statement(1).entry, destination->checked_out) == at(statement(1).entry, count(pool_object(destination, _)));
    }
    fold(pool_object(destination, object));
    frame() using {
    }
    have 0 <= source->checked_out and source->checked_out <= source->capacity and source->checked_out == count(pool_object(source, _)) by {
        unfold(valid_pool);
        have 0 <= source->checked_out and source->checked_out <= source->capacity by {
            unfold(valid_pool);
            have 0 <= source->checked_out by {
                unfold(valid_pool);
                rewrite(at(statement(2).entry, 1) == at(statement(2).entry, count(pool_object(source, object))));
                rewrite(at(statement(0).entry, source->checked_out) == at(statement(0).entry, count(pool_object(source, _))));
                normalize();
            }
            have source->checked_out <= source->capacity by {
                unfold(valid_pool);
                have 0 <= at(statement(0).entry, source->checked_out) by {
                    rewrite(at(statement(0).entry, source->checked_out) == at(statement(0).entry, count(pool_object(source, _))));
                    rewrite(at(statement(2).entry, count(pool_object(source, object))) == at(statement(2).entry, 1));
                    normalize();
                }
                apply(int32_nonnegative_predecessor_upper_bound(at(statement(0).entry, source->checked_out), at(statement(0).entry, source->capacity))) using {
                    0 <= at(statement(0).entry, source->checked_out);
                    at(statement(0).entry, source->checked_out) <= at(statement(0).entry, source->capacity);
                }
                assumption();
            }
            split();
        }
        have source->checked_out == count(pool_object(source, _)) by {
            unfold(valid_pool);
            rewrite(at(statement(0).entry, 1) == at(statement(0).entry, count(pool_object(source, object))));
            rewrite(at(statement(0).entry, source->checked_out) == at(statement(0).entry, count(pool_object(source, _))));
            normalize();
        }
        split();
    }
    have 0 <= destination->checked_out and destination->checked_out <= destination->capacity and destination->checked_out == count(pool_object(destination, _)) by {
        unfold(valid_pool);
        have 0 <= destination->checked_out and destination->checked_out <= destination->capacity by {
            unfold(valid_pool);
            have 0 <= destination->checked_out by {
                unfold(valid_pool);
                rewrite(at(statement(1).entry, destination->checked_out) == at(statement(1).entry, count(pool_object(destination, _))));
                normalize();
            }
            have destination->checked_out <= destination->capacity by {
                unfold(valid_pool);
                apply(int32_increment_upper_bound(at(statement(1).entry, destination->checked_out), at(statement(1).entry, destination->capacity))) using {
                    at(statement(1).entry, destination->checked_out) < at(statement(1).entry, destination->capacity);
                }
                assumption();
            }
            split();
        }
        have destination->checked_out == count(pool_object(destination, _)) by {
            unfold(valid_pool);
            rewrite(at(statement(1).entry, destination->checked_out) == at(statement(1).entry, count(pool_object(destination, _))));
            normalize();
        }
        split();
    }
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
}

void pool_destroy(struct pool* pool) {
    requires valid_pool(pool);
    requires pool->checked_out == 0;
    owns object(pool);
    mutable pool->capacity;

    ensures valid_pool(pool);
    ensures pool->capacity == 0;
} by {
    unfold(valid_pool);
    execute();
    have valid_pool(pool) by {
        unfold(valid_pool);
        simp();
    }
    frame();
    simp();
}

void pool_pipeline(
    struct pool* pool,
    struct object* first,
    struct object* second
) {
    owns object(pool);
    owns object(first);
    owns object(second);
    mutable pool->checked_out, pool->capacity, first->value, second->value;

    ensures valid_pool(pool);
    ensures pool->checked_out == 0;
    ensures pool->capacity == 0;
    ensures first->value == 11;
    ensures second->value == 22;
} by {
    step();
    step();
    step();
    unfold(valid_pool);
    open(pool_object(pool, first)) {
        step() using {
            0 <= pool->checked_out;
            pool->checked_out <= pool->capacity;
            pool->checked_out == count(pool_object(pool, _));
        }
    }
    open(pool_object(pool, second)) {
        step() using {
            0 <= pool->checked_out;
            pool->checked_out <= pool->capacity;
            pool->checked_out == count(pool_object(pool, _));
        }
    }
    mark after_object_writes;
    step() using {
        loadable(pool->checked_out);
        loadable(pool->capacity);
        0 <= pool->checked_out;
        pool->checked_out <= pool->capacity;
        pool->checked_out == count(pool_object(pool, _));
    }
    transport(
        at(after_object_writes, first->value == 11),
        first->value == 11
    );
    transport(
        at(after_object_writes, second->value == 22),
        second->value == 22
    );
    unfold(valid_pool);
    step() using {
        loadable(pool->checked_out);
        loadable(pool->capacity);
        0 <= pool->checked_out;
        pool->checked_out <= pool->capacity;
        pool->checked_out == count(pool_object(pool, _));
    }
    unfold(valid_pool);
    have pool->checked_out == 0 by simp;
    step() using {
        loadable(pool->checked_out);
        loadable(pool->capacity);
        0 <= pool->checked_out;
        pool->checked_out <= pool->capacity;
        pool->checked_out == count(pool_object(pool, _));
        pool->checked_out == 0;
        first->value == 11;
        second->value == 22;
    }
    step();
    frame();
    have pool->capacity == 0 by {
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

void pool_transfer_pipeline(
    struct pool* source,
    struct pool* destination,
    struct object* object
) {
    requires source != destination;
    owns object(source);
    owns object(destination);
    owns object(object);
    mutable source->checked_out, source->capacity,
        destination->checked_out, destination->capacity;
    produces pool_object(destination, object);

    ensures valid_pool(source);
    ensures valid_pool(destination);
    ensures source->checked_out == 0;
    ensures source->capacity == 1;
    ensures destination->checked_out == 1;
    ensures destination->capacity == 1;
} by {
    step();
    step();
    step();
    step();
    step();
    frame();
    have source->checked_out == 0 by {
        assumption();
    }
    have source->capacity == 1 by {
        assumption();
    }
    have destination->checked_out == 1 by {
        assumption();
    }
    have destination->capacity == 1 by {
        assumption();
    }
    have valid_pool(source) by {
        unfold(valid_pool);
        simp();
    }
    have valid_pool(destination) by {
        unfold(valid_pool);
        simp();
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
}
