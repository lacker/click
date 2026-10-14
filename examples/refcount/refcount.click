authorized resource reference(obj: struct object*) {}

resource control(obj: struct object*) {
    owns allocation(obj, sizeof(struct object));
    owns *obj;
    owns authority(reference(obj));
    fact obj->refs == count(reference(obj));
}

verifying "object_init.c";
verifying "object_retain.c";
verifying "object_release_nonfinal.c";
verifying "object_release_final.c";

void object_init(struct object* obj) {
    consumes *obj;
    produces *obj;
    ensures obj->refs == 1;
    ensures defined(obj->refs);
} by {
    execute();
    simp();
}

void object_retain(struct object* obj) {
    owns control(obj);
    requires obj->refs < 2147483647;
    produces reference(obj);
} by {
    open(control(obj)) {
        step();
        fold(reference(obj));
    }
    execute();
    simp();
}

void object_release_nonfinal(struct object* obj) {
    owns control(obj);
    consumes reference(obj);
    requires obj->refs > 1;
} by {
    open(control(obj)) {
        unfold(reference(obj));
        step();
    }
    execute();
    simp();
}

void object_release_final(struct object* obj) {
    requires obj->refs == 1;
    consumes control(obj);
    consumes reference(obj);
} by {
    unfold(control(obj));
    unfold(reference(obj));
    unfold(authority(reference(obj)));
    execute();
    simp();
}

verifying "object_retain_many.c";
verifying "object_release_many_nonfinal.c";

void object_retain_many(struct object* obj, int32 amount) {
    requires 0 <= amount;
    requires defined(obj->refs + amount);
    owns control(obj);
    produces amount of reference(obj);
    ensures defined(obj->refs);
} by {
    open(control(obj)) {
        step();
        fold(amount of reference(obj));
    }
    execute();
    simp();
}

void object_release_many_nonfinal(struct object* obj, int32 amount) {
    requires 0 <= amount;
    requires amount < obj->refs;
    requires defined(1 + amount);
    owns control(obj);
    consumes amount of reference(obj);
    ensures defined(obj->refs);
} by {
    open(control(obj)) {
        unfold(amount of reference(obj));
        step();
    }
    execute();
    simp();
}

verifying "refcount_pipeline.c";

int32 refcount_pipeline(int32 amount) {
    requires 0 <= amount;
    requires amount <= 2147483646;
    ensures result == -1 or result == 0;
} by {
    have defined(1 + amount) by auto;
    step();
    step();
    branch then {
        step();
        simp();
    } else {}
    step();
    have defined(obj->refs + amount) by auto;
    fold(authority(reference(obj)));
    fold(reference(obj));
    fold(control(obj));
    step();
    open(control(obj)) {
    }
    have amount < obj->refs by auto;
    step();
    open(control(obj)) {
    }
    step();
    step();
    simp();
}
