resource object_ref(obj: struct object*) {
    contains allocation(obj, sizeof(struct object));
    owns object(obj);
    fact obj->refs == count(object_ref(obj));
}

verifying "object_init.c";
verifying "object_retain.c";
verifying "object_retain_many.c";
verifying "object_release_nonfinal.c";
verifying "object_release_many_nonfinal.c";
verifying "object_release_final.c";
verifying "refcount_pipeline.c";

void object_init(struct object* obj) {
    consumes allocation(obj, sizeof(struct object));
    consumes object(obj);
    mutable obj->refs;
    produces object_ref(obj);
} by {
    execute();
    fold(object_ref(obj));
    frame();
    simp();
}

void object_retain(struct object* obj) {
    requires obj->refs < 2147483647;
    owns object_ref(obj);
    produces object_ref(obj);
    mutable obj->refs;
} by {
    open(object_ref(obj)) {
        execute();
        frame();
    }
    simp();
}

void object_retain_many(struct object* obj, int32 amount) {
    requires 0 <= amount;
    requires defined(1 + amount);
    owns object_ref(obj);
    produces amount of object_ref(obj);
    mutable obj->refs;
} by {
    open(object_ref(obj)) {
        have 1 == obj->refs by simp;
        execute();
        frame();
    }
    have 1 <= 1 + amount by {
        apply(int32_add_nonnegative_right_is_at_least_left(1, amount)) using {
            0 <= amount;
            defined(1 + amount);
        }
    }
    have amount <= 1 + amount by {
        apply(int32_add_nonnegative_left_is_at_least_right(1, amount)) using {
            defined(1 + amount);
        }
    }
    simp();
}

void object_release_nonfinal(struct object* obj) {
    requires 1 < obj->refs;
    owns object_ref(obj);
    consumes object_ref(obj);
    mutable obj->refs;
} by {
    open(object_ref(obj)) {
        execute();
        frame();
    }
    simp();
}

void object_release_many_nonfinal(struct object* obj, int32 amount) {
    requires 0 <= amount;
    requires amount < obj->refs;
    requires defined(1 + amount);
    owns object_ref(obj);
    consumes amount of object_ref(obj);
    mutable obj->refs;
} by {
    open(object_ref(obj)) {
        have amount <= obj->refs by {
            apply(int32_lt_implies_le(amount, obj->refs)) using {
                amount < obj->refs;
            }
        }
        have defined(obj->refs - amount) by {
            apply(int32_nonnegative_subtract_within_value_is_defined(obj->refs, amount)) using {
                0 <= amount;
                amount <= obj->refs;
            }
        }
        have defined(1 + amount) and obj->refs == 1 + amount by {
            split();
        }
        have obj->refs - amount == 1 by {
            apply(int32_subtract_equal_sum_right_cancels(obj->refs, 1, amount)) using {
                defined(1 + amount) and obj->refs == 1 + amount;
                defined(obj->refs - amount);
            }
        }
        execute();
        frame();
    }
    simp();
}

void object_release_final(struct object* obj) {
    requires obj->refs == 1;
    consumes object_ref(obj);
    mutable obj->refs;
} by {
    unfold(object_ref(obj));
    execute();
    frame();
    simp();
}

int32 refcount_pipeline(int32 amount) {
    requires 0 <= amount;
    requires amount <= 2147483646;
    ensures result == -1 or result == 0;
} by {
    have amount < 2147483647 by simp;
    have defined(1 + amount) by {
        apply(int32_one_plus_below_max_is_defined(amount)) using {
            amount < 2147483647;
        }
    }
    have amount <= 1 + amount by {
        apply(int32_add_nonnegative_left_is_at_least_right(1, amount)) using {
            defined(1 + amount);
        }
    }
    have amount < 1 + amount by {
        apply(int32_one_plus_strictly_increases(amount)) using {
            amount < 2147483647;
        }
    }
    have defined((1 + amount) - amount) by {
        apply(int32_nonnegative_subtract_within_value_is_defined(1 + amount, amount)) using {
            0 <= amount;
            amount <= 1 + amount;
        }
        split();
    }
    step();
    step();
    branch {
        then {
            step();
            simp();
        }
        else {}
    }
    step();
    step() using {
        0 <= amount;
        defined(1 + amount);
    }
    have obj->refs == 1 + amount by simp;
    have amount < obj->refs by {
        rewrite(obj->refs == 1 + amount);
        assumption();
    }
    step() using {
        0 <= amount;
        amount <= 1 + amount;
        amount < obj->refs;
        defined(1 + amount);
        defined((1 + amount) - amount);
    }
    step();
    step();
    simp();
}
