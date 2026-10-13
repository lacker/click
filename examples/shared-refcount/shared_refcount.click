target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "shared_refcount.c";
authorized resource reference(obj: struct object*) {}
authorized resource permit(obj: struct object*) {}
resource control(obj: struct object*) {
    field refs: int32;
    field slack: int32;
    owns obj->refs;
    owns authority(reference(obj));
    owns authority(permit(obj));
    fact obj->refs == refs;
    fact refs == count(reference(obj));
    fact slack == count(permit(obj));
    fact to_integer(refs) + to_integer(slack) == 3;
}
void object_retain(struct object *obj) {
    owns access: mutex_use(&obj->mu, control(obj));
    consumes permit(obj);
    produces reference(obj);
} by {
    let { guard: guard, state: state } = step(pthread_mutex_lock(&obj->mu), { access: access });
    let { refs: refs, slack: slack } = unfold(state);
    have count(permit(obj)) >= 1;
    have slack == count(permit(obj));
    have to_integer(1) <= to_integer(slack) by auto;
    have to_integer(refs) <= to_integer(2) by arithmetic() using {
        to_integer(refs) + to_integer(slack) == 3;
        to_integer(1) <= to_integer(slack);
    };
    have refs <= 2 by auto;
    have to_integer(refs + 1) == to_integer(refs) + to_integer(1) by auto;
    have to_integer(slack - 1) == to_integer(slack) - to_integer(1) by auto;
    have to_integer(refs + 1) + to_integer(slack - 1) == 3 by arithmetic() using {
        to_integer(refs + 1) == to_integer(refs) + to_integer(1);
        to_integer(slack - 1) == to_integer(slack) - to_integer(1);
        to_integer(refs) + to_integer(slack) == 3;
    };
    unfold(permit(obj));
    fold(reference(obj));
    step();
    let restored = fold(control(obj), { refs: refs + 1, slack: slack - 1 });
    step(pthread_mutex_unlock(&obj->mu), { access: access, guard: guard, state: restored });
    step();
    simp();
}
void object_release(struct object *obj) {
    owns access: mutex_use(&obj->mu, control(obj));
    consumes reference(obj);
    produces permit(obj);
} by {
    let { guard: guard, state: state } = step(pthread_mutex_lock(&obj->mu), { access: access });
    let { refs: refs, slack: slack } = unfold(state);
    have count(reference(obj)) >= 1;
    have refs == count(reference(obj));
    have to_integer(1) <= to_integer(refs) by auto;
    have to_integer(slack) <= to_integer(2) by arithmetic() using {
        to_integer(refs) + to_integer(slack) == 3;
        to_integer(1) <= to_integer(refs);
    };
    have slack <= 2 by auto;
    have to_integer(refs - 1) == to_integer(refs) - to_integer(1) by auto;
    have to_integer(slack + 1) == to_integer(slack) + to_integer(1) by auto;
    have to_integer(refs - 1) + to_integer(slack + 1) == 3 by arithmetic() using {
        to_integer(refs - 1) == to_integer(refs) - to_integer(1);
        to_integer(slack + 1) == to_integer(slack) + to_integer(1);
        to_integer(refs) + to_integer(slack) == 3;
    };
    unfold(reference(obj));
    fold(permit(obj));
    step();
    let restored = fold(control(obj), { refs: refs - 1, slack: slack + 1 });
    step(pthread_mutex_unlock(&obj->mu), { access: access, guard: guard, state: restored });
    step();
    simp();
}
void* user(void* argument) {
    owns access: mutex_use(&((struct object*)argument)->mu, control((struct object*)argument));
    consumes reference((struct object*)argument);
    produces permit((struct object*)argument);
} by {
    step();
    step();
    step(object_release(obj), { access: access });
    step();
    simp();
}
int32 run() {
    ensures result == -1 or result == 0 or result == 1;
} by {
    step();
    step();
    step();
    step();
    branch then { step(); simp(); } else {}
    step();
    fold(authority(reference(obj)));
    fold(authority(permit(obj)));
    fold(reference(obj));
    fold(permit(obj));
    fold(permit(obj));
    let control = fold(control(obj), { refs: 1, slack: 2 });
    let { lifetime: lifetime } = step(pthread_mutex_init(&obj->mu, 0), { state: control });
    step(object_retain(obj), { access: lifetime });
    step();
    branch then {
        step(object_release(obj), { access: lifetime });
        step(object_release(obj), { access: lifetime });
        step(pthread_mutex_destroy(&obj->mu), { lifetime: lifetime });
        unfold(control);
        unfold(permit(obj));
        unfold(permit(obj));
        unfold(permit(obj));
        unfold(authority(reference(obj)));
        unfold(authority(permit(obj)));
        step();
        step();
        simp();
    } else {}
    step(object_retain(obj), { access: lifetime });
    step();
    branch then {
        step(object_release(obj), { access: lifetime });
        step();
        step(object_release(obj), { access: lifetime });
        step(pthread_mutex_destroy(&obj->mu), { lifetime: lifetime });
        unfold(control);
        unfold(permit(obj));
        unfold(permit(obj));
        unfold(permit(obj));
        unfold(authority(reference(obj)));
        unfold(authority(permit(obj)));
        step();
        step();
        simp();
    } else {}
    step();
    step();
    step(object_release(obj), { access: lifetime });
    step(pthread_mutex_destroy(&obj->mu), { lifetime: lifetime });
    unfold(control);
    unfold(permit(obj));
    unfold(permit(obj));
    unfold(permit(obj));
    unfold(authority(reference(obj)));
    unfold(authority(permit(obj)));
    step();
    step();
    simp();
}

int32 run_reverse_join() {
    ensures result == -1 or result == 0 or result == 1;
} by {
    step();
    step();
    step();
    step();
    branch then { step(); simp(); } else {}
    step();
    fold(authority(reference(obj)));
    fold(authority(permit(obj)));
    fold(reference(obj));
    fold(permit(obj));
    fold(permit(obj));
    let control = fold(control(obj), { refs: 1, slack: 2 });
    let { lifetime: lifetime } = step(pthread_mutex_init(&obj->mu, 0), { state: control });
    step(object_retain(obj), { access: lifetime });
    step();
    branch then {
        step(object_release(obj), { access: lifetime });
        step(object_release(obj), { access: lifetime });
        step(pthread_mutex_destroy(&obj->mu), { lifetime: lifetime });
        unfold(control);
        unfold(permit(obj));
        unfold(permit(obj));
        unfold(permit(obj));
        unfold(authority(reference(obj)));
        unfold(authority(permit(obj)));
        step();
        step();
        simp();
    } else {}
    step(object_retain(obj), { access: lifetime });
    step();
    branch then {
        step(object_release(obj), { access: lifetime });
        step();
        step(object_release(obj), { access: lifetime });
        step(pthread_mutex_destroy(&obj->mu), { lifetime: lifetime });
        unfold(control);
        unfold(permit(obj));
        unfold(permit(obj));
        unfold(permit(obj));
        unfold(authority(reference(obj)));
        unfold(authority(permit(obj)));
        step();
        step();
        simp();
    } else {}
    step();
    step();
    step(object_release(obj), { access: lifetime });
    step(pthread_mutex_destroy(&obj->mu), { lifetime: lifetime });
    unfold(control);
    unfold(permit(obj));
    unfold(permit(obj));
    unfold(permit(obj));
    unfold(authority(reference(obj)));
    unfold(authority(permit(obj)));
    step();
    step();
    simp();
}
