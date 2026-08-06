resource service(owner: struct service*) {
    owns owner->phase;
    owns owner->cell;
    owns owner->cell[0..1];
    fact 0 <= owner->phase;
    fact owner->phase <= 1;
    fact owner->cell[0] == owner->phase;
    fact separate(memory(object(owner)), memory(owner->cell[0..1]));
}

verifying "service_init.c";
verifying "service_step.c";
verifying "service_run.c";

int32 service_init(struct service* owner, int32 cell[]) {
    consumes object(owner);
    consumes cell[0..1];
    mutable owner->phase, owner->cell, cell[0..1];
    produces service(owner);

    ensures result == 0;
    ensures owner->phase == 0;
    ensures owner->cell == cell;
    ensures owner->cell[0] == 0;
} by {
    execute();
    fold(service(owner));
    frame();
    simp();
}

int32 service_step(struct service* owner) {
    owns service(owner);
    mutable owner->phase, owner->cell[0..1];

    ensures result == owner->phase;
    ensures 0 <= owner->phase;
    ensures owner->phase <= 1;
    ensures owner->cell[0] == owner->phase;
} by {
    unfold(service(owner));
    execute();
    fold(service(owner));
    frame();
    simp();
}

int32 service_run(struct service* owner) {
    owns service(owner);
} by {
    step();
    loop {
        invariant 0 <= owner->phase;
        invariant owner->phase <= 1;
        mutable owner->phase, owner->cell[0..1] by {
            frame() using {
                separate(memory(object(owner)), memory(owner->cell[0..1]));
            }
        }

        initialize by simp;
        preserve by {
            step() using {};
            close_invariants();
        }
    }
    simp();
}
