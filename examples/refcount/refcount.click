counted resource object_ref(obj: struct object*) {
    contains allocation(obj, sizeof(struct object));
    owns object(obj);
    fact obj->refs == count(object_ref(obj));
}

verifying "object_init.c";
verifying "object_retain.c";
verifying "object_release_nonfinal.c";
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
    execute();
    frame();
    simp();
}

void object_release_nonfinal(struct object* obj) {
    requires 1 < obj->refs;
    owns object_ref(obj);
    consumes object_ref(obj);
    mutable obj->refs;
} by {
    execute();
    frame();
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

int32 refcount_pipeline() {
    ensures result == -1 or result == 0;
} by {
    step();
    step();
    branch {
        then {
            step();
            simp();
        }
        else {
        }
    }
    step();
    step();
    step();
    have obj->refs == 1 by {
        assumption();
    }
    step() using {
        obj->refs == 1;
    }
    step();
    simp();
}
